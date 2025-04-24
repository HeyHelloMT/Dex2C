#!/usr/bin/env python
# coding=utf-8
import argparse
import os
import re
import sys
import json
import subprocess
from logging import getLogger, INFO, StreamHandler, Formatter
from androguard.core import androconf
from androguard.core.analysis import analysis
from androguard.core.bytecodes import dvm
from androguard.util import read
from dex2c.compiler import Dex2C
from dex2c.util import (
    JniLongName,
    get_method_triple,
    get_access_method,
    is_synthetic_method,
    is_native_method,
)
from random import choice
from string import ascii_letters, digits
from shutil import rmtree, copytree, copy

# Setup logging
logger = getLogger("dcc")
logger.setLevel(INFO)
handler = StreamHandler()
handler.setFormatter(Formatter('%(levelname)s: %(message)s'))
logger.addHandler(handler)

# Constants
SKIP_SYNTHETIC_METHODS = False
NDK_BUILD_CMD = "ndk-build"

def get_random_str(length=8):
    characters = ascii_letters + digits
    return "".join(choice(characters) for _ in range(length))

def make_temp_dir(prefix="dcc"):
    os.makedirs(".tmp", exist_ok=True)
    while True:
        random_str = get_random_str()
        tmp = os.path.join(".tmp", prefix + random_str)
        if not os.path.exists(tmp):
            os.makedirs(tmp)
            return tmp

def clean_tmp_directory():
    tmpdir = ".tmp"
    if os.path.exists(tmpdir):
        rmtree(tmpdir)

def load_config():
    config = {}
    if os.path.exists("dcc.cfg"):
        with open("dcc.cfg") as fp:
            config = json.load(fp)
    return config

class MethodFilter:
    def __init__(self, configure, vm):
        self._compile_filters = []
        self._keep_filters = []
        self._compile_full_match = set()
        self.conflict_methods = set()
        self.native_methods = set()
        self.annotated_methods = set()
        self._load_filter_configure(configure)
        self._init_conflict_methods(vm)
        self._init_native_methods(vm)
        self._init_annotation_methods(vm)

    def _load_filter_configure(self, configure):
        if not os.path.exists(configure):
            return

        with open(configure) as fp:
            for line in fp:
                line = line.strip()
                if not line or line[0] == "#":
                    continue
                if line[0] == "!":
                    line = line[1:].strip()
                    self._keep_filters.append(re.compile(line))
                elif line[0] == "=":
                    line = line[1:].strip()
                    self._compile_full_match.add(line)
                else:
                    self._compile_filters.append(re.compile(line))

    def _init_conflict_methods(self, vm):
        all_methods = {}
        for m in vm.get_methods():
            method_triple = get_method_triple(m, return_type=False)
            if method_triple in all_methods:
                self.conflict_methods.add(m)
                self.conflict_methods.add(all_methods[method_triple])
            else:
                all_methods[method_triple] = m

    def _init_native_methods(self, vm):
        for m in vm.get_methods():
            cls_name, name, _ = get_method_triple(m)
            access = get_access_method(m.get_access_flags())
            if "native" in access:
                self.native_methods.add((cls_name, name))

    def _add_annotation_method(self, method):
        if not is_synthetic_method(method) and not is_native_method(method):
            self.annotated_methods.add(method)

    def _init_annotation_methods(self, vm):
        for c in vm.get_classes():
            adi_off = c.get_annotations_off()
            if adi_off == 0:
                continue

            adi = vm.CM.get_obj_by_offset(adi_off)
            if adi.get_class_annotations_off() != 0:
                ann_set_item = vm.CM.get_obj_by_offset(adi.get_class_annotations_off())
                for aoffitem in ann_set_item.get_annotation_off_item():
                    annotation_item = vm.CM.get_obj_by_offset(aoffitem.get_annotation_off())
                    type_desc = vm.CM.get_type(annotation_item.get_annotation().get_type_idx())
                    if type_desc.endswith("Dex2C;"):
                        for method in c.get_methods():
                            self._add_annotation_method(method)
                        break

            for mi in adi.get_method_annotations():
                method = vm.get_method_by_idx(mi.get_method_idx())
                ann_set_item = vm.CM.get_obj_by_offset(mi.get_annotations_off())
                for aoffitem in ann_set_item.get_annotation_off_item():
                    annotation_item = vm.CM.get_obj_by_offset(aoffitem.get_annotation_off())
                    type_desc = vm.CM.get_type(annotation_item.get_annotation().get_type_idx())
                    if type_desc.endswith("Dex2C;"):
                        self._add_annotation_method(method)

    def should_compile(self, method):
        if method in self.conflict_methods:
            return False
        if is_synthetic_method(method) and SKIP_SYNTHETIC_METHODS:
            return False
        if is_native_method(method):
            return False

        method_triple = get_method_triple(method)
        cls_name, name, _ = method_triple

        if name == "<clinit>":
            return False

        if (cls_name, name) in self.native_methods:
            return False

        full_name = "".join(method_triple)
        for rule in self._keep_filters:
            if rule.search(full_name):
                return False

        if full_name in self._compile_full_match:
            return True

        if method in self.annotated_methods:
            return True

        for rule in self._compile_filters:
            if rule.search(full_name):
                return True

        return False

def write_compiled_methods(project_dir, compiled_methods):
    source_dir = os.path.join(project_dir, "jni", "nc")
    os.makedirs(source_dir, exist_ok=True)

    for method_triple, code in compiled_methods.items():
        full_name = JniLongName(*method_triple)
        filepath = os.path.join(source_dir, full_name) + ".cpp"
        if os.path.exists(filepath):
            logger.warning(f"Overwriting file {filepath} for method {method_triple}")

        try:
            with open(filepath, "w", encoding="utf-8") as fp:
                fp.write('#include "Dex2C.h"\n' + code)
        except Exception as e:
            logger.error(f"Error writing {filepath}: {str(e)}")

    with open(os.path.join(source_dir, "compiled_methods.txt"), "w", encoding="utf-8") as fp:
        fp.write("\n".join("".join(m) for m in compiled_methods.keys()))

def write_dynamic_register(project_dir, compiled_methods, method_prototypes):
    source_dir = os.path.join(project_dir, "jni", "nc")
    os.makedirs(source_dir, exist_ok=True)
    
    export_list = {}
    for method_triple in sorted(compiled_methods.keys()):
        full_name = JniLongName(*method_triple)
        if full_name not in method_prototypes:
            raise Exception(f"Method {full_name} prototype info not found")
        
        class_path = method_triple[0][1:-1].replace(".", "/")
        method_name = method_triple[1]
        method_signature = method_triple[2]
        method_native_name = full_name
        method_native_prototype = method_prototypes[full_name]
        
        if class_path not in export_list:
            export_list[class_path] = []
        export_list[class_path].append(
            (method_name, method_signature, method_native_name, method_native_prototype)
        )

    if not export_list:
        logger.info("No export methods for dynamic registration")
        return

    extern_block = []
    export_block = ["\njclass clazz;\n"]
    export_block_template = (
        'clazz = env->FindClass("%s");\n'
        'if (clazz == nullptr)\n    return "Class not found: %s";\n'
        "const JNINativeMethod export_method_%d[] = {\n%s\n};\n"
        "env->RegisterNatives(clazz, export_method_%d, %d);\n"
        "env->DeleteLocalRef(clazz);\n"
    )
    
    for index, class_path in enumerate(sorted(export_list.keys())):
        methods = export_list[class_path]
        extern_block.extend(f"extern {method[3]};" for method in methods)
        export_methods = ",\n".join(
            f'{{"{method[0]}", "{method[1]}", (void *){method[2]}}}' 
            for method in methods
        )
        export_block.append(
            export_block_template % (
                class_path, class_path, index, export_methods, index, len(methods)
            )
        )
    
    export_block.append("return nullptr;\n")
    
    filepath = os.path.join(source_dir, "DynamicRegister.cpp")
    with open(filepath, "w", encoding="utf-8") as fp:
        fp.write('#include "DynamicRegister.h"\n\n')
        fp.write("\n".join(extern_block))
        fp.write("\n\nconst char *dynamic_register_compile_methods(JNIEnv *env) {")
        fp.write("\n".join(export_block))
        fp.write("}")

def compile_dex(dexfile, filtercfg, obfus, dynamic_register):
    try:
        dex = dvm.DalvikVMFormat(read(dexfile))
        dex_analysis = analysis.Analysis()
        dex_analysis.add(dex)

        method_filter = MethodFilter(filtercfg, dex)
        compiler = Dex2C(dex, dex_analysis, obfus, dynamic_register)

        compiled_methods = {}
        method_prototypes = {}
        errors = []

        for m in dex.get_methods():
            method_triple = get_method_triple(m)
            jni_longname = JniLongName(*method_triple)
            full_name = "".join(method_triple)

            if len(jni_longname) > 220:
                logger.debug(f"Name too long {jni_longname}(>220) {full_name}")
                continue

            if method_filter.should_compile(m):
                logger.debug(f"Compiling {full_name}")
                try:
                    code = compiler.get_source_method(m)
                except Exception as e:
                    error_msg = f"{full_name}:{str(e)}"
                    logger.warning(f"Compile method failed: {error_msg}")
                    errors.append(error_msg)
                    continue

                if code[0]:
                    compiled_methods[method_triple] = code[0]
                    method_prototypes[jni_longname] = code[1]

        return compiled_methods, method_prototypes, errors
    except Exception as e:
        logger.error(f"Error processing DEX file: {str(e)}")
        raise

def run_ndk_build(project_dir):
    jni_dir = os.path.join(project_dir, "jni")
    if not os.path.exists(jni_dir):
        raise Exception(f"JNI directory not found at {jni_dir}")

    logger.info("Starting NDK build...")
    try:
        result = subprocess.run(
            [NDK_BUILD_CMD, "-C", project_dir],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True
        )
        logger.info("NDK build output:\n" + result.stdout)
        return True
    except subprocess.CalledProcessError as e:
        logger.error(f"NDK build failed:\n{e.stdout}")
        return False
    except Exception as e:
        logger.error(f"Error running NDK build: {str(e)}")
        return False

def prepare_project_template(project_dir):
    if not os.path.exists("project"):
        raise Exception("Project template directory 'project' not found")
    
    if os.path.exists(project_dir):
        rmtree(project_dir)
    
    copytree("project", project_dir)
    return project_dir

def process_dex_file(
    dexfile, 
    filtercfg="filter.txt", 
    obfus=False, 
    dynamic_register=False,
    output_dir=None
):
    if not os.path.exists(dexfile):
        raise Exception(f"DEX file not found: {dexfile}")

    if not os.path.exists(filtercfg):
        logger.warning(f"Filter config file {filtercfg} not found, using all methods")

    # Prepare project directory
    project_dir = output_dir if output_dir else make_temp_dir("dcc-project-")
    prepare_project_template(project_dir)

    # Compile DEX to C
    compiled_methods, method_prototypes, errors = compile_dex(
        dexfile, filtercfg, obfus, dynamic_register
    )

    if errors:
        logger.warning("Compilation errors:\n" + "\n".join(errors))

    if not compiled_methods:
        logger.error("No methods compiled! Check your filter file.")
        return None

    # Write compiled methods
    write_compiled_methods(project_dir, compiled_methods)

    # Handle dynamic registration if enabled
    if dynamic_register:
        write_dynamic_register(project_dir, compiled_methods, method_prototypes)
    else:
        # Write empty dynamic register file if not used
        with open(os.path.join(project_dir, "jni", "nc", "DynamicRegister.cpp"), "w") as f:
            f.write('#include "DynamicRegister.h"\n\nconst char *dynamic_register_compile_methods(JNIEnv *) { return nullptr; }')

    # Run NDK build
    if not run_ndk_build(project_dir):
        raise Exception("NDK build failed")

    return project_dir

def modify_dex_with_native_stubs(dexfile, compiled_methods, output_dex):
    """
    Modify the DEX file to replace compiled methods with native stubs
    """
    try:
        # Load the original DEX
        with open(dexfile, 'rb') as f:
            dex_data = f.read()
        
        # Parse DEX
        dv = dvm.DalvikVMFormat(dex_data)
        
        # For each method that was compiled to native code
        for method_triple in compiled_methods.keys():
            class_name, method_name, proto = method_triple
            
            # Find the class
            class_def = None
            for c in dv.get_classes():
                if c.get_name() == class_name:
                    class_def = c
                    break
            
            if class_def:
                # Find the method
                for method in class_def.get_methods():
                    m_name = method.get_name()
                    m_proto = method.get_descriptor()
                    
                    if m_name == method_name and m_proto == proto:
                        # Make the method native
                        access_flags = method.get_access_flags()
                        access_flags |= 0x100  # ACC_NATIVE flag
                        method.set_access_flags(access_flags)
                        
                        # Clear the method code (since it's now native)
                        method.set_code_off(0)
        
        # Save the modified DEX
        with open(output_dex, 'wb') as f:
            f.write(dv.save())
            
        return True
        
    except Exception as e:
        print(f"Error modifying DEX: {str(e)}")
        return False

def main():
    parser = argparse.ArgumentParser(description="DEX to C++ Converter")
    parser.add_argument("-i", "--input", required=True, help="Input DEX file path")
    parser.add_argument("-f", "--filter", default="filter.txt", help="Method filter configuration file")
    parser.add_argument("-o", "--output", help="Output directory for compiled code")
    parser.add_argument("-p", "--obfuscate", action="store_true", help="Obfuscate string constants")
    parser.add_argument("-d", "--dynamic-register", action="store_true", help="Use dynamic method registration")
    parser.add_argument("--skip-synthetic", action="store_true", help="Skip synthetic methods")

    args = parser.parse_args()

    global SKIP_SYNTHETIC_METHODS
    SKIP_SYNTHETIC_METHODS = args.skip_synthetic

    # Load NDK path from config if available
    config = load_config()
    if config.get("ndk_dir"):
        global NDK_BUILD_CMD
        NDK_BUILD_CMD = os.path.join(config["ndk_dir"], "ndk-build")

    try:
        clean_tmp_directory()
        os.makedirs(".tmp", exist_ok=True)

        # 1. Process DEX file and generate C++ code
        project_dir = process_dex_file(
            args.input,
            args.filter,
            args.obfuscate,
            args.dynamic_register,
            args.output
        )

        if not project_dir:
            logger.error("Processing failed")
            sys.exit(1)

        # 2. Create modified DEX with native stubs
        output_dex_path = os.path.join(project_dir, "modified.dex")
        if not modify_dex_with_native_stubs(args.input, get_compiled_methods(project_dir), output_dex_path):
            logger.error("Failed to create modified DEX")
            sys.exit(1)

        logger.info(f"Processing complete. Output directory: {project_dir}")
        logger.info(f"Modified DEX: {output_dex_path}")
        logger.info(f"Shared libraries: {os.path.join(project_dir, 'libs')}")

    except Exception as e:
        logger.error(f"Error: {str(e)}")
        sys.exit(1)
    finally:
        if not args.output:  # Only clean temp dir if we created it
            clean_tmp_directory()

def get_compiled_methods(project_dir):
    methods = []
    with open(os.path.join(project_dir, "jni", "nc", "compiled_methods.txt")) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            
            # More robust parsing that handles all method signature cases
            if '->' in line and '(' in line:
                try:
                    class_part, rest = line.split('->', 1)
                    method_part, proto_part = rest.split('(', 1)
                    methods.append((class_part, method_part, '(' + proto_part))
                except ValueError:
                    logger.warning(f"Skipping malformed method signature: {line}")
            else:
                logger.warning(f"Skipping invalid method format: {line}")
    return methods

if __name__ == "__main__":
    main()