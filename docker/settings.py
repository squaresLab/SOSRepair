"""
This file includes all the settings that could be modified for running SearchRepair/SOSRepair

* LIBCLANG_PATH: The path to libclang build. It should be either a .so or .dylib file.
* GENERATE_DB_PATH: The path where the DB should be built from. SR will enumerate all C files in this path to build the
 DB
* Z3_COMMAND: The z3 command on this machine.
* LARGEST_SNIPPET: The maximum number of lines that is considered as a snippet.
* SMALLEST_SNIPPET: The minimum number of lines that is considered as a snippet.
* DATABASE: Information about the database.
* LOGGING: Settings for logging.
* MAX_SUSPICIOUS_LINES: The number of suspicious lines tried before giving up.
* VALID_TYPES: The variable types that are right now supported by SR.
------ Settings related to file under repair -------
* TESTS_LIST: The path to a list of the tests that could be run on the file
* TEST_SCRIPT: The path to a script that will run the test
* COMPILE_SCRIPT: The path to a script that will compile the code
* FAULTY_CODE: The path to the faulty code (a C file)
* COMPILE_EXTRA_ARGS: The list of necessary arguments that should be passed to clang to properly parse the code
* MAKE_OUTPUT: The output of running `make` stored in a file (for the purpose of finding necessary arguments for compilation
automatically)
* METHOD_RANGE: The tuple of beginning and end of method with the fault (limits the search to the area)
* SOSREPAIR: If set to False it will only run SearchRepair features
* NUMBER_OF_TIMES_RERUNNING_TESTS: The number of times that the tests should be run to assure patch's correctness
* EXCLUDE_SCANF: If removing/replacing scanf in buggy code is going to be a problem, set this to True
"""
__author__ = 'Afsoon Afzal'

import logging


LIBCLANG_PATH = '/opt/sosrepair/llvm/lib/libclang.so'

GENERATE_DB_PATH = '/experiment/IntroClass/median/aaceaf4ad658a90db957967d2852b7dfa81b42f4ab8dbdf2f7c9847a6072e1741a6b0cbd2ea52f5669f2da1cdf925ec565d257320cf93b97bc9bc99f000e1871'

Z3_COMMAND = '/opt/sosrepair/bin/z3'

LARGEST_SNIPPET = 7
SMALLEST_SNIPPET = 3

DATABASE = {
    'db_name': 'testdocker',
    'user': 'docker',
    'password': '1234'
}

LOGGING = {
    'filename': 'logs/repair.log',
    'level': logging.DEBUG
}

logging.basicConfig(**LOGGING)

MAX_SUSPICIOUS_LINES = 10

VALID_TYPES = ['int', 'short', 'long', 'char', 'float', 'double', 'long long', 'size_t']

TESTS_LIST = "/experiment/project-repair/tests-list.txt"
TEST_SCRIPT = "/experiment/project-repair/test.sh"
TEST_SCRIPT_TYPE = "/bin/bash"
COMPILE_SCRIPT = "/experiment/project-repair/compile.sh"
FAULTY_CODE = "/experiment/project-repair/median.c"


COMPILE_EXTRA_ARGS = [
                    "-I/usr/include",
#                    "-I/home/afsoon/llvm/build/lib/clang/3.9.0/include"
]

MAKE_OUTPUT = ""

METHOD_RANGE = (0, 1000000)

SOSREPAIR = True

NUMBER_OF_TIMES_RERUNNING_TESTS = 1
EXCLUDE_SCANF = False

BULK_RUN_PATH = "/experiment/project-repair"
