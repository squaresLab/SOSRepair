__author__ = 'afsoona'

import os
import logging
from math import sqrt
from utils.c_run import *
from settings import TESTS_DIRECTORY

logger = logging.getLogger(__name__)


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
            run_command('rm ' + get_plain_name_without_directory(self.plain_name) + '.gcda')
            res = run_c_with_input_provided(self.plain_name, test)
            if not res:
                logger.error("Coverage failed on this test %s" % test)
                self.use_gdb_for_gcov(self.plain_name, test)
            run_command_with_timeout('gcov --object-directory ./ ' + self.program)

            try:
                self.parse_gcov_file(get_plain_name_without_directory(self.filename) + '.gcov', pos_or_neg)
            except IOError:
                logger.error("No gcov file found")
                continue
        run_command('rm ' + get_plain_name_without_directory(self.filename) + '.* ')

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

    @staticmethod
    def use_gdb_for_gcov(filename, test):
        with open('gdb_script.txt', 'w') as f:
            f.write('file ' + filename + '\n')
            f.write('run ' + test + '\n')
            f.write('call exit()\nquit\n')
        run_command_with_timeout_interrupt('gdb < gdb_script.txt')
        run_command('rm gdb_script.txt')

