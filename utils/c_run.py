__author__ = 'afsoona'

import os

def get_plain_name(filename):
    parts = filename.split('.')
    plain_name = filename[0:-1*(len(parts[-1])+1)]
    return plain_name

def run_command(command):
    #TODO time restriction
    res = os.system(command)
    if res != 0:
        return False
    return True

def compile_c(program, run_file_name, options=None):
    #TODO time restriction
    if options:
        command = 'gcc ' + options + ' -o ' + run_file_name + ' ' + program
    else:
        command = 'gcc -o ' + run_file_name + ' ' + program
    res = os.system(command)
    if res != 0:
        return False
    return True


def run_c_with_input(run_file_name, input, output=None):
    #TODO time restriction
    if output:
        command = './' + run_file_name + ' < ' + input + ' > ' + output
    else:
        command = './' + run_file_name + ' < ' + input
    res = os.system(command)
    if res != 0:
        return False
    return True