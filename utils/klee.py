__author__ = 'Afsoon Afzal'

import os
import subprocess
from utils.c_run import run_command


def compile_clang(filename, extra_args):
    command = "clang-3.4 " + " ".join(extra_args) + " -emit-llvm -c -g " + filename
    res = run_command(command)
    if not res:
        return False
    return True


def run_klee(filename, output_dir='klee-out'):
    try:
        i = filename.rfind('.c')
        filename = filename[:i]+'.bc'
    except:
        return False
    if os.path.exists(output_dir):
        os.system('rm -r ' + output_dir)

    proc = subprocess.Popen(["klee", "-use-query-log=all:smt2", "-write-smt2s", "-libc=uclibc", "-use-constant-arrays",
                             "-const-array-opt", "-allow-external-sym-calls", "-watchdog", "-max-time=2",
                             "-output-dir="+output_dir, filename], stdout=subprocess.PIPE)
    (out, err) = proc.communicate()
    if err:
        return 0
    with open(os.path.join(output_dir, 'info'), 'r') as f:
        for l in f:
            if l.startswith('KLEE: done: generated tests ='):
                k = l.rfind('=')
                test_nums = int(l[k+1:])
                return test_nums
    return 0


def read_smt_files(path_number, klee_dir='klee-out'):
    file_name = klee_dir + '/test' + ('0'*(6-len(str(path_number)))) + str(path_number) + '.smt2'
    with open(file_name, 'r') as file:
        return file.read()

