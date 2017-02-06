__author__ = 'afsoona'

import os
import subprocess
import threading
from utils import timeout as timeout_function, kill_check, timeout_interrupt


def get_plain_name(filename):
    parts = filename.split('.')
    plain_name = filename[0:-1*(len(parts[-1])+1)]
    return plain_name


def get_name_without_directory(filename):
    parts = filename.split('/')
    plain_name = parts[-1]
    return plain_name


def run_command(command):
    res = os.system(command)
    if res != 0:
        return False
    return True


def run_command_with_timeout(command, timeout=5):
    proc = subprocess.Popen(command, shell=True, preexec_fn=os.setsid)
    t = threading.Timer(timeout, timeout_function, [proc])
    t.start()
    (out, err) = proc.communicate()
    t.cancel()
    print "return code %d" % int(proc.returncode) 
    if err or kill_check.isSet() or proc.returncode:
        kill_check.clear()
        return False
    return True


def run_command_with_timeout_get_output(command, timeout=5):
    proc = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, preexec_fn=os.setsid)
    t = threading.Timer(timeout, timeout_function, [proc])
    t.start()
    (out, err) = proc.communicate()
    t.cancel()
    if err or kill_check.isSet() or proc.returncode:
        kill_check.clear()
        return None
    return out


def compile_c(program, run_file_name, options=None):
    if options:
        command = 'gcc ' + options + ' -o ' + run_file_name + ' ' + program
    else:
        command = 'gcc -o ' + run_file_name + ' ' + program
    return run_command_with_timeout(command)


def run_c_with_input(run_file_name, input, output=None):
    if output:
        command = '' + run_file_name + ' < ' + input + ' > ' + output
    else:
        command = '' + run_file_name + ' < ' + input
    return run_command_with_timeout(command)


def run_c_with_input_provided(run_file_name, input):
    command = run_file_name + ' ' + input
    return run_command_with_timeout(command)


def run_command_with_timeout_interrupt(command, timeout=5):
    proc = subprocess.Popen(command, shell=True, preexec_fn=os.setsid)
    t = threading.Timer(timeout, timeout_interrupt, [proc])
    t.start()
    (out, err) = proc.communicate()
    t.cancel()
    if err or kill_check.isSet():
        kill_check.clear()
        return False
    return True
