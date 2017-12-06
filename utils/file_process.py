__author__ = 'afsoona'

import difflib
import subprocess
from utils.c_run import run_command
from settings import COMPILE_EXTRA_ARGS


def number_of_lines(filename):
    proc = subprocess.Popen(["wc", "-l", filename], stdout=subprocess.PIPE)
    (out, err) = proc.communicate()
    return int(out.strip(' ').split(' ')[0])


def compare_files(file1, file2):
    with open(file1, 'r') as hosts0:
        with open(file2, 'r') as hosts1:
            diff = difflib.unified_diff(
                hosts0.readlines(),
                hosts1.readlines(),
                fromfile='hosts0',
                tofile='hosts1',
            )
            for line in diff:
                return False
    return True


def transform_file(filename):
    transformed_file = filename + '_trans.c'
    success = run_command("sed '/^\s*$/d' %s > %s" % (filename, transformed_file))
    return transformed_file


def find_extra_compile_args(output_file, compiled_file):
    with open(output_file, "r") as f:
        for l in f:
            if compiled_file in l:
                splits = l.split(" ")
                extra_args = []
                for s in splits:
                    if s.startswith("-I"):
                        if s.startswith("-I/usr/include"):
                            extra_args.append("-I/home/afsoon/llvm/build/lib/clang/3.9.0/include")
                        else:
                            extra_args.append(s)
                return extra_args
    return COMPILE_EXTRA_ARGS


def find_includes(filename):
    includes = ''
    with open(filename, "r") as f:
        for l in f:
            if l.startswith("#include"):
                includes += l
    return includes


def get_file_name_and_module_re(filename=''):
    index = filename.find('src')
    if index != -1:
        filename = filename[index+4:]  # removing src/ and before
    index = filename.rfind('/')
    module = filename
    if index != -1:
        module = module[:index+1] + ".*"
    return filename, module
