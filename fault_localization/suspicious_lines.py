__author__ = 'afsoona'

import os
import logging
import random
from math import sqrt
from utils.c_run import *
from settings import *

logger = logging.getLogger(__name__)


class SuspiciousLines():
    """
    Generates a sorted list of program lines based on their suspiciousness.
    """
    def __init__(self, tests):
        self.suspiciousness = []
        self.counts = {}
        self.tests = tests

    def compute_suspiciousness(self):
        self.compute_coverage(self.tests.positives, '+')
        self.compute_coverage(self.tests.negatives, '-')
        self.suspicious_formula()

        def custom_cmp(item1, item2):
            if item1[1] != item2[1]:
                return cmp(item1[1], item2[1])
            else:
                return -1 if random.random() >= 0.5 else 1

        self.suspiciousness.sort(cmp=custom_cmp, reverse=True)
        return

    def compute_coverage(self, test_list, pos_or_neg):
        for test in test_list:
            run_command('rm ' + get_plain_name(FAULTY_CODE) + '.gcda')
            try:
                if GCOV_OBJECTS:
                    run_command('rm ' + GCOV_OBJECTS + '/*.gcda')
            except NameError:
                pass
            run_command('rm ' + get_name_without_directory(FAULTY_CODE) + '.gcov')
            res = run_command_with_timeout(TEST_SCRIPT + ' ' + test, 50)
            if not res:
                logger.debug("test %s" %str(test))
                continue
                #TODO
                logger.error("Coverage failed on this test %s" % test)
                self.use_gdb_for_gcov(test)
            try:
                if GCOV_OBJECTS:
                    run_command('gcov -o ' + GCOV_OBJECTS + '/ ' + FAULTY_CODE)
                else:
                    run_command_with_timeout('gcov ' + FAULTY_CODE)
            except NameError:
                pass
            else:
                run_command_with_timeout('gcov ' + FAULTY_CODE)

            try:
                self.parse_gcov_file(get_name_without_directory(FAULTY_CODE) + '.gcov', pos_or_neg)
            except IOError:
                logger.error("No gcov file found")
                continue
        run_command('rm ' + get_name_without_directory(FAULTY_CODE) + '.* ')

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
    def use_gdb_for_gcov(test):
        with open('gdb_script.txt', 'w') as f:
            f.write('file ' + TEST_SCRIPT_TYPE + '\n')
            f.write('''
set detach-on-fork off
set non-stop on
set pagination on
set target-async on
set confirm off
''')
            f.write('set args ' + TEST_SCRIPT + ' ' + test + '\n')
            f.write('run\n')
            #f.write('''
#interrupt -a
#thread apply all call exit()
#thread all apply kill
#quit
#''')
        run_command_with_timeout_interrupt('gdb --command=gdb_script.txt', 30)
        #run_command('rm gdb_script.txt')

