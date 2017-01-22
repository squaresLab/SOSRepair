__author__ = 'afsoona'

import difflib
import subprocess
from utils.c_run import run_command


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
#    run_command("./remccoms3.sed < " + filename + ' >  tempfile')
    with open(filename, 'r') as f:
        with open(transformed_file, 'w') as tf:
            for l in f:
                if l.isspace():
                    continue
                tf.write(l)
    run_command('rm tempfile')
    return transformed_file


def find_extra_compile_args(output_file, compiled_file):
    with open(output_file, "r") as f:
        for l in f:
            if compiled_file in l:
                splits = l.split(" ")
                extra_args = []
                for s in splits:
                    if s.startswith("-I"):
                        extra_args.append(s)
                return extra_args
    return []
