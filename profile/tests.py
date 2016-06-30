__author__ = 'afsoona'

import os
import logging

from settings import TESTS_DIRECTORY
from utils.file_process import compare_files
from utils.c_run import compile_c, run_c_with_input, get_plain_name, run_command_with_timeout, run_command

logger = logging.getLogger(__name__)

class Tests():

    def __init__(self, program_name, test_script):
        self.test_script = test_script
        self.program_name = program_name
        self.plain_name = get_plain_name(program_name)
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
        res = compile_c(self.program_name, self.plain_name)
        if not res:
            # raise Exception
            return False
        temp_output = self.plain_name + '_temp.out'
        run_command('rm ' + temp_output)
        command = self.test_script + ' ' + self.plain_name + ' ' + temp_output
        res = run_command_with_timeout(command, 10)
        if not res:
            return False
        with open(temp_output, 'r') as f:
            for l in f:
                if l.startswith('+'):
                    self.positives.append(l[1:].strip())
                elif l.startswith('-'):
                    self.negatives.append(l[1:].strip())
                else:
                    logger.error("Unexpected output in tests")
                    return False
        return True

    def __str__(self):
        return "Positives: " + str(self.positives) + "\nNegative: " + str(self.negatives)

    def __unicode__(self):
        return "Positives: " + str(self.positives) + "\nNegative: " + str(self.negatives)