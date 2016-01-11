__author__ = 'afsoona'

import os


def compile_c(program, run_file_name):
    #TODO time restriction
    res = os.system('gcc -o ' + run_file_name + ' ' + program)
    if res != 0:
        return False
    return True


def run_c_with_input(run_file_name, input, output):
    #TODO time restriction
    res = os.system('./' + run_file_name + ' < ' + input + ' > ' + output)
    if res != 0:
        return False
    return True