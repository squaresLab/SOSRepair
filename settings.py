"""
This file includes all the settings that could be modified for running SearchRepair/SOSRepair

* LIBCLANG_PATH: The path to libclang build. It should be either a .so or .dylib file.
* GENERATE_DB_PATH: The path where the DB should be built from. SR will enumerate all C files in this path to build the
 DB
* Z3_COMMAND: The z3 command on this machine.
* LARGEST_SNIPPET: The maximum number of lines that is considered as a snippet.
* SMALLEST_SNIPPET: The minimum number of lines that is considered as a snippet.
* DATABASE: Information about the database.
* ALL_PATCHES: If False, SR will return the first found patch, otherwise it will try to find more.
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


# LIBCLANG_PATH = '/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/libclang.dylib'
LIBCLANG_PATH = '/home/afsoon/llvm/build/lib/libclang.so'
# LIBCLANG_PATH = '/Users/afsoona/llvm/build/lib/libclang.dylib'

GENERATE_DB_PATH = '/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src'

Z3_COMMAND = '/home/afsoon/z3/build/z3'

LARGEST_SNIPPET = 7
SMALLEST_SNIPPET = 3

DATABASE = {
    'db_name': 'testsmallest',
    'user': 'afsoon',
    'password': None
}

ALL_PATCHES = False

LOGGING = {
    'filename': 'logs/repair.log',
    'level': logging.DEBUG
}

logging.basicConfig(**LOGGING)

MAX_SUSPICIOUS_LINES = 10

VALID_TYPES = ['int', 'short', 'long', 'char', 'float', 'double', 'long long', 'size_t']

TESTS_LIST = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/tests-list.txt"
TEST_SCRIPT = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/test.sh a"
TEST_SCRIPT_TYPE = "/bin/bash"
COMPILE_SCRIPT = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/compile.sh"
FAULTY_CODE = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/main/streams/streams.c"


COMPILE_EXTRA_ARGS = [
                    "-DPHP_ATOM_INC",
                    "-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src",
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/TSRM',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/Zend',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/ext',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/include',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/main',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/main/',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/main/streams/',
                    "-I/usr/include/libxml2",
                    "-I/usr/include",
#                    "-I/home/afsoon/llvm/build/lib/clang/3.9.0/include"
]

MAKE_OUTPUT = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-12-10-74343ca506-52c36e60c4/src/makeout"

METHOD_RANGE = (975, 1045)

SOSREPAIR = True

NUMBER_OF_TIMES_RERUNNING_TESTS = 1
EXCLUDE_SCANF = False
