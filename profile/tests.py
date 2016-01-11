__author__ = 'afsoona'

import os

from settings import TESTS_DIRECTORY
from utils.file_process import compare_files
from utils.c_run import compile_c, run_c_with_input

class Tests():

    def __init__(self, program_directory, program_name):
        self.program_directory = program_directory
        self.program_name = program_name
        parts = program_name.split('.')
        self.plain_name = program_name[0:-1*(len(parts[-1]))]
        self.positives = []
        self.negatives = []


    def initialize_testing(self):
        program = os.path.join(self.program_directory, self.program_name)
        res = compile_c(program, self.plain_name)
        if not res:
            raise Exception
        temp_output = os.path.join(self.program_directory, self.plain_name + '_temp.out')
        test_files = os.listdir(TESTS_DIRECTORY)
        for file in test_files:
            if not file.endswith('.in'):
                continue
            test = os.path.join(TESTS_DIRECTORY, file)
            res = run_c_with_input(self.plain_name, test, temp_output)
            if not res:
                raise Exception
            out_file = file[0:-3]+'.out'
            if compare_files(os.path.join(TESTS_DIRECTORY, out_file), temp_output):
                self.positives.append(file)
            else:
                self.negatives.append(file)
        os.system('rm ' + temp_output + ' ' + self.plain_name)
        return True

    def __str__(self):
        return "Positives: " + str(self.positives) + "\nNegative: " + str(self.negatives)

    def __unicode__(self):
        return "Positives: " + str(self.positives) + "\nNegative: " + str(self.negatives)