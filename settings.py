__author__ = 'Afsoon Afzal'

import logging

#LIBCLANG_PATH = '/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/libclang.dylib'
LIBCLANG_PATH = '/home/afsoon/llvm/build/lib/libclang.so'
#LIBCLANG_PATH = '/Users/afsoona/llvm/build/lib/libclang.dylib'

TESTS_DIRECTORY = '/home/afsoon/Documents/workspace/SCS/IntroClass/median/tests/blackbox'
INTROCLASS_PATH = './IntroClass/median'

Z3_COMMAND = '/home/afsoon/Documents/z3/build/z3'

LARGEST_SNIPPET = 7
SMALLEST_SNIPPET = 3

DATABASE = {
    'db_name': 'testdb',
    'user': 'afsoon',
    'password': None
}

ALL_PATCHES = False

LOGGING = {
    'filename': 'logs/repair.log',
    'level': logging.DEBUG
}

logging.basicConfig(**LOGGING)

MAX_SUSPICIOUS_LINES = 5

VALID_TYPES = ['int', 'short', 'long', 'char', 'float', 'double', 'long long']

TESTS_LIST = "/home/afsoon/Documents/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/gzip/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1/tests-list.txt"
TEST_SCRIPT = "/home/afsoon/Documents/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/gzip/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1/test.sh a"
TEST_SCRIPT_TYPE = "/bin/bash"
COMPILE_SCRIPT = "/home/afsoon/Documents/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/gzip/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1/compile.sh"
FAULTY_CODE = "/home/afsoon/Documents/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/gzip/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1/gzip/gzip.c"


