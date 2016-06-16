__author__ = 'afsoona'

import os
import subprocess
import threading
from utils import timeout as timeout_function, kill_check


def get_plain_name(filename):
    parts = filename.split('.')
    plain_name = filename[0:-1*(len(parts[-1])+1)]
    return plain_name


def run_command(command):
    res = os.system(command)
    if res != 0:
        return False
    return True


def run_command_with_timeout(command, timeout=10):
    proc = subprocess.Popen(command, shell=True)
    t = threading.Timer(timeout, timeout_function, [proc])
    t.start()
    (out, err) = proc.communicate()
    t.cancel()
    if err or kill_check.isSet():
        kill_check.clear()
        return False
    return True


def compile_c(program, run_file_name, options=None):
    if options:
        command = 'gcc ' + options + ' -o ' + run_file_name + ' ' + program
    else:
        command = 'gcc -o ' + run_file_name + ' ' + program
    return run_command_with_timeout(command)


def run_c_with_input(run_file_name, input, output=None):
    if output:
        command = './' + run_file_name + ' < ' + input + ' > ' + output
    else:
        command = './' + run_file_name + ' < ' + input
    return run_command_with_timeout(command)
