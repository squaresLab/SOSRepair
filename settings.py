__author__ = 'Afsoon Afzal'

import logging

#LIBCLANG_PATH = '/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/libclang.dylib'
LIBCLANG_PATH = '/home/afsoon/llvm/build/lib/libclang.so'
#LIBCLANG_PATH = '/Users/afsoona/llvm/build/lib/libclang.dylib'

TESTS_DIRECTORY = '/home/afsoon/Documents/workspace/SCS/IntroClass/median/tests/blackbox'
INTROCLASS_PATH = '/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/python/python-original/python'

Z3_COMMAND = '/home/afsoon/z3/build/z3'

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

MAX_SUSPICIOUS_LINES = 10

VALID_TYPES = ['int', 'short', 'long', 'char', 'float', 'double', 'long long']

TESTS_LIST = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/python/python-original/tests-list1.txt"
TEST_SCRIPT = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/python/python-original/test.sh a"
TEST_SCRIPT_TYPE = "/bin/bash"
COMPILE_SCRIPT = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/python/python-original/compile1.sh"
FAULTY_CODE = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/python/python-original/python/Modules/selectmodule.c"


