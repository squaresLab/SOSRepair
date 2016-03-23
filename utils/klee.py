__author__ = 'Afsoon Afzal'

import os
import subprocess


def compile_clang(filename):
    command = "clang-3.4 -emit-llvm -c -g " + filename
    res = os.system(command)
    if res != 0:
        return False
    return True


def run_klee(filename, output_dir='klee-out'):
    try:
        i = filename.rfind('.c')
        filename = filename[:i]+'.bc'
    except:
        return False
    proc = subprocess.Popen(["klee", "-use-query-log=all:smt2", "-write-smt2s", "-libc=uclibc", "-use-constant-arrays",
                             "-const-array-opt", "-output-dir=", output_dir, filename], stdout=subprocess.PIPE)
    (out, err) = proc.communicate()
    if err:
        return 0
    for l in out:
        if l.startswith('KLEE: done: generated tests ='):
            k = l.rfind('=')
            test_nums = int(l[k+1:])
            return test_nums
    return 0


