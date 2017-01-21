__author__ = 'Afsoon Afzal'

import os
import subprocess
from utils.c_run import run_command


def compile_clang(filename):
    command = "clang-3.4 -I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php/include -I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php/main -I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php -I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php/ext/date/lib -I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php/ext/ereg/regex -I/usr/include/libxml2 -I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php/ext/sqlite3/libsqlite -I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php/TSRM -I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php/Zend -I/usr/include -L/usr/lib/x86_64-linux-gnu -emit-llvm -c -g " + filename
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

