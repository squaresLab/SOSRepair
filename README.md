# SearchRepair #

SearchRepair is an automatic program repair tool which tries to fix programs with the help of both generate-and-validate
and semantics-based techniques.

### Requirements ###

You can use `docker` to build a container that already has all the
requirements installed and ready to go.

* KLEE - You need to have KLEE up and running in your system. Find the
instruction of how to install KLEE on your system [here](http://klee.github.io/build-llvm34/).
SR has been confirmed to work on KLEE version 1.2 on using llvm 3.
* llvm and clang - You need to install llvm and clang by source to be
able to modify and extend it later. [Instruction](http://llvm.org/docs/GettingStarted.html).
SR has been confirmed to work on llvm commit \(db55668\) and clang commit \(2a0e7716\).
Updating llvm and clang to their latest version should not have an effect on SearchRepair.
Before building llvm and clang from source, apply the patch in `docker/0001-Binary-operation.patch`
to clang. This patch will add a functionality to python bindings that
are needed for SR. After building llvm and clang, set your `PYTHONPATH`
to include clang python bindings.
* Postgres
We will use Postgres as our database. Make sure you also install it's python binding (psycopg). You can
 install it using pip.
* Z3 SMT solver
You can install it from [here](https://github.com/Z3Prover/z3).

### Set-up ###

* Create a database on postgres using the command `createdb <testdb>`. 
(**Note:** If you are receiving errors like `role “username” does not exist`
you need to create user and role for postgres. [Here](https://stackoverflow.com/questions/11919391/postgresql-error-fatal-role-username-does-not-exist)
you can find the instruction on how to do that.)
* Edit `settings.py` file and edit based on your settings.
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
    * ------ Settings related to file under repair -------
    * TESTS_LIST: The path to a list of the tests that could be run on the file
    * TEST_SCRIPT: The path to a script that will run the test
    * COMPILE_SCRIPT: The path to a script that will compile the code
    * FAULTY_CODE: The path to the faulty code (a C file)
    * COMPILE_EXTRA_ARGS: The list of necessary arguments that should be passed to clang to properly parse the code
    * MAKE_OUTPUT: The output of running `make` stored in a file (for the purpose of finding necessary arguments for compilation
    automatically)
    * METHOD_RANGE: The tuple of beginning and end of method with the fault (limits the search to the area)
    * SOSREPAIR: If set to False it will only run SearchRepair features

### Running ###

* If you need to generate database go to file `run.py` and at the end of file edit the call to `main()` to `main(True)`
otherwise just leave it te way it is
* If you wish to remove logs from previous runs delete `logs/repair.log`.
* Run `python2.7 run.py`
* Whenever tool finds a patch it will put the patch inside folder `patches`
that is created at runtime

