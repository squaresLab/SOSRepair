__author__ = 'Afsoon Afzal'

import logging

# LIBCLANG_PATH = '/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/libclang.dylib'
LIBCLANG_PATH = '/home/afsoon/llvm/build/lib/libclang.so'
# LIBCLANG_PATH = '/Users/afsoona/llvm/build/lib/libclang.dylib'

TESTS_DIRECTORY = '/home/afsoon/Documents/workspace/SCS/IntroClass/median/tests/blackbox'
INTROCLASS_PATH = '/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src'

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

TESTS_LIST = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/tests-list.txt"
TEST_SCRIPT = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/test.sh a"
TEST_SCRIPT_TYPE = "/bin/bash"
COMPILE_SCRIPT = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/compile.sh"
FAULTY_CODE = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c-master/many-bugs/php/php-original/php/Zend/zend_compile.c"


COMPILE_EXTRA_ARGS = [
                    "-DPHP_ATOM_INC",
                    "-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src",
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src/TSRM',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src/Zend',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src/ext',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src/include',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src/main',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src/main/',
                    '-I/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src/main/streams/',
                    "-I/usr/include/libxml2",
                    "-I/usr/include",
                    "-I/home/afsoon/llvm/build/lib/clang/3.9.0/include"
]

MAKE_OUTPUT = "/home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/many-bugs/php/php-bug-2011-01-30-5bb0a44e06-1e91069eb4/src/makeout"
