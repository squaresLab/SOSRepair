__author__ = 'afsoona'

import os
from math import sqrt
from utils.c_run import *
from settings import TESTS_DIRECTORY

class SuspiciousLines():

    def __init__(self, filename, directory, tests):
        self.suspiciousness = []
        self.counts = {}
        self.filename = filename
        self.directory = directory
        self.program = os.path.join(self.directory, self.filename)
        self.plain_name = get_plain_name(filename)
        self.tests = tests

    def compute_suspiciousness(self):
        res = compile_c(self.program, self.plain_name, ' -fprofile-arcs -ftest-coverage ')
        if not res:
            raise Exception
        self.compute_coverage(self.tests.positives, '+')
        self.compute_coverage(self.tests.negatives, '-')
        run_command('rm ' + self.plain_name + ' ' + self.plain_name + '.gcno')
        self.suspicious_formula()
        self.suspiciousness.sort(key=lambda tuple: tuple[1], reverse=True)
        return

    def compute_coverage(self, test_list, pos_or_neg):
        for test in test_list:
            test_path = os.path.join(TESTS_DIRECTORY, test)
            run_command('rm ' + self.plain_name + '.gcda')
            res = run_c_with_input(self.plain_name, test_path)
            if not res:
                raise Exception
            run_command_with_timeout('gcov --object-directory ./ ' + self.program)
            self.parse_gcov_file(self.filename + '.gcov', pos_or_neg)
        run_command('rm ' + self.filename + '.* ')

    def parse_gcov_file(self, gcov_file, pos_or_neg):
        with open(gcov_file, 'r') as f:
            for l in f:
                if not l:
                    continue
                l = l.strip()
                segments = l.split(':')
                line_number = int(segments[1])
                if line_number == 0:
                    continue
                frequency = segments[0]
                if frequency.startswith('-') or frequency.startswith('#'):
                    continue
                else:
                    current = self.counts.get(line_number)
                    if current:
                        current[pos_or_neg] += 1
                    else:
                        self.counts[line_number] = {'+': 0, '-': 0}
                        self.counts[line_number][pos_or_neg] += 1

    def suspicious_formula(self):
        total_fail = len(self.tests.negatives)
        for line_number in self.counts.keys():
            failed = self.counts[line_number]['-']
            passed = self.counts[line_number]['+']
            denom = total_fail * (failed + passed)
            left = failed * 1.0 / total_fail
            right = failed * 1.0 / (failed + passed)
            if denom == 0:
                self.suspiciousness.append((line_number, 0.0))
            else:
                self.suspiciousness.append((line_number, sqrt(left * right)))




