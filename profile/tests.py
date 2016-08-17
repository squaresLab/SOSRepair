__author__ = 'afsoona'

import os
import logging

from settings import *
from utils.file_process import compare_files
from utils.c_run import compile_c, run_c_with_input, run_command_with_timeout, run_command, run_command_with_timeout_get_output

logger = logging.getLogger(__name__)

class Tests():

    def __init__(self):
        self.tests_list = []
        with open(TESTS_LIST, 'r') as f:
            for l in f:
                self.tests_list.append(l.strip())
        self.positives = []
        self.negatives = []

    def initialize_testing(self):
        program = self.program_name
        res = compile_c(program, self.plain_name)
        if not res:
            # raise Exception
            return False
        temp_output = self.plain_name + '_temp.out'
        test_files = os.listdir(TESTS_DIRECTORY)
        for file in test_files:
            if not file.endswith('.in'):
                continue
            test = os.path.join(TESTS_DIRECTORY, file)
            res = run_c_with_input(self.plain_name, test, temp_output)
            if not res:
                self.negatives.append(file)
                continue
            out_file = file[0:-3]+'.out'
            if compare_files(os.path.join(TESTS_DIRECTORY, out_file), temp_output):
                self.positives.append(file)
            else:
                self.negatives.append(file)
                print file + " " + temp_output
        os.system('rm ' + temp_output + ' ' + self.plain_name)
        return True

    def initialize_script_testing(self):
        res = run_command_with_timeout(COMPILE_SCRIPT, timeout=50)
        if not res:
            return False
        for test in self.tests_list:
            res = run_command_with_timeout_get_output(TEST_SCRIPT + ' ' + test)
            if not res:
                self.negatives.append(test)
                logger.error("Test failed!") # Fix me
                continue
            for l in res.splitlines():
                if l.startswith("PASS"):
                    self.positives.append(test)
                    break
                elif l.startswith("FAIL"):
                    self.negatives.append(test)
                    break
        return True

    def __str__(self):
        return "Positives: " + str(self.positives) + "\nNegative: " + str(self.negatives)

    def __unicode__(self):
        return "Positives: " + str(self.positives) + "\nNegative: " + str(self.negatives)
