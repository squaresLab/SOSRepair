__author__ = 'Afsoon Afzal'

import os
import logging

from settings import *
from utils.file_process import compare_files
from utils.c_run import compile_c, run_c_with_input, run_command_with_timeout, run_command, run_command_with_timeout_get_output

logger = logging.getLogger(__name__)

class Tests():
    """
    Tests contains information related to tests on original program.
    """
    def __init__(self):
        self.tests_list = []
        with open(TESTS_LIST, 'r') as f:
            for l in f:
                self.tests_list.append(l.strip())
        self.positives = []
        self.negatives = []

    def initialize_script_testing(self):
        res = run_command_with_timeout(COMPILE_SCRIPT, timeout=70)
        print "RES %s" % str(res)
        if not res:
            return False
        for test in self.tests_list:
            print "running test %s" %test
            res = run_command_with_timeout_get_output(TEST_SCRIPT + ' ' + test, timeout=70)
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

    def rerun_tests(self):
        """
        Reruns the tests.
        :return: False the moment a test fails, True if all tests pass
        """
        res = run_command_with_timeout(COMPILE_SCRIPT, timeout=70)
        print "RES %s" % str(res)
        if not res:
            return False
        all_tests = self.negatives[:]
        all_tests.extend(self.positives[:])
        for test in all_tests:
            print "running test %s" %test
            res = run_command_with_timeout_get_output(TEST_SCRIPT + ' ' + test, timeout=70)
            if not res:
                logger.error("Test failed!") # Fix me
                return False
            for l in res.splitlines():
                if l.startswith("PASS"):
                    break
                elif l.startswith("FAIL"):
                    return False
        return True

    def __str__(self):
        return "Positives: " + str(self.positives) + "\nNegative: " + str(self.negatives)

    def __unicode__(self):
        return "Positives: " + str(self.positives) + "\nNegative: " + str(self.negatives)
