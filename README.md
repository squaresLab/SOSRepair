# SOSRepair #

SOSRepair is an automatic program repair tool which tries to fix programs with the help of both generate-and-validate
and semantics-based techniques.

### Requirements ###

You can use `docker` to build a container that already has all the
requirements installed and ready to go. Simply run
`docker build -t squareslab/sosrepair:latest .`.

* KLEE - You need to have KLEE up and running in your system. Find the
instruction of how to install KLEE on your system [here](http://klee.github.io/build-llvm34/).
SOSRepair has been confirmed to work on KLEE version 1.2 on using llvm 3.
* llvm and clang - You need to install llvm and clang by source to be
able to modify and extend it later. [Instruction](http://llvm.org/docs/GettingStarted.html).
SOSORepair has been confirmed to work on llvm commit \(db55668\) and clang commit \(2a0e7716\).
Updating llvm and clang to their latest version should not have an effect on SOSRepair.
Before building llvm and clang from source, apply the patch in `docker/0001-Binary-operation.patch`
to clang. This patch will add a functionality to python bindings that
are needed for SOSRepair. After building llvm and clang, set your `PYTHONPATH`
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
    * GENERATE_DB_PATH: The path where the DB should be built from. SOSRepair will enumerate all C files in this path to build the DB.
    * Z3_COMMAND: The z3 command on this machine.
    * LARGEST_SNIPPET: The maximum number of lines that is considered as a snippet.
    * SMALLEST_SNIPPET: The minimum number of lines that is considered as a snippet.
    * DATABASE: Information about the database.
    * ALL_PATCHES: If False, SR will return the first found patch, otherwise it will try to find more.
    * LOGGING: Settings for logging.
    * MAX_SUSPICIOUS_LINES: The number of suspicious lines tried before giving up.
    * VALID_TYPES: The variable types that are right now supported by SOSRepair.
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

An example of `settings.py` file for a simple defect exists in `docker/settings.py`.

## Running ##

### Locally ###

* Run `python2.7 run.py -h` to see all the options of running SOSRepair. Overall, there are two modes for running (specified by `--run_mode`): `normal` and `bulk_run`. By default, the run mode is set to `normal` which will attempt to repair the file specified as `FAULTY_CODE` in the `settings.py` file. On `bulk_run` mode, SOSRepair attempts to repair all `.C` files in the `GENERATE_DB_PATH` directory and report how many of those it was able to repair.
There are three options for interacting with the database (specified by `--db`): `none`, `build_and_run`, `build`. By default this option is set to `none` which means it will not rebuild the database and will only read from it. Option `build` specifies that you only want to rebuild the database and you do not want to start the repair. Option `build_and_run` specifies that the repair will automatically start after rebuilding the database. Pay attention that `build` and `build_and_run` options automatically wipe out the data currently in the database and repopulate it with new data. 
* If you wish to remove logs from previous runs delete `logs/repair.log`.
* Whenever tool finds a patch it will put the patch inside folder `patches`
that is created at runtime

### Using Docker ###

To simplify running SOSRepair, we have created a `Dockerfile` that creates a docker image
with all requirements already installed and a small sample program to fix. Simply run
`docker build -t squareslab/sosrepair:latest .` to build the docker image.

When finished, you can create a docker container and attach to it by running
`docker run --rm -it squareslab/sosrepair /bin/bash`. You will then find SOSRepair under
`/opt/sosrepair/sosrepair`, and a simple defect under `/experiment/project-repair`.
Before running SOSRepair make sure that you execute `/opt/sosrepair/prepare/setup.sh`,
start the postgresql engine `sudo /etc/init.d/postgresql start`, and create a database
`createdb testdocker`. Modify `settings.py` file in `/opt/sosrepair/sosrepair` to match
your database info, and run SOSRepair as you would run locally.

### Using BugZoo ###

[BugZoo](https://github.com/squaresLab/BugZoo) is a decentralized platform for distributing,
reproducing, and interacting with historical software bugs, and allows the user to run
different program repair tools on known benchmarks using docker containers. SOSRepair
is set up to be consistent with BugZoo, and can be added as a source. After installing
BugZoo, simply run `bugzoo source add sosrepair https://github.com/squaresLab/SOSRepair`.
If this step goes well, you should be able to see sosrepair as a tool listed in BugZoo by
running `bugzoo tool list`.

Next, you need to build SOSRepair docker image: `bugzoo tool build sosrepair`. In addition,
you need to install bugs that you wish to run SOSRepair on as described [here](https://github.com/squaresLab/BugZoo). For example, to add ManyBugs to BugZoo, run `bugzoo source add manybugs https://github.com/squaresLab/ManyBugs`. To build a bug run `bugzoo bug build <bug-name>` (e.g., `bugzoo bug build manybugs:libtiff:2005-12-14-6746b87-0d3d51d`).

When both the bug and the tool are built, you can launch a container that contains both
SOSRepair and the specified bug: `bugzoo container launch --with sosrepair --net host manybugs:libtiff:2005-12-14-6746b87-0d3d51d`. The launched container now contains SOSRepair under
`/opt/sosrepair/sosrepair` and the bug under `/experiment`. Take similar steps as running
SOSRepair Docker.

Notes:
* If you received errors related to permissions, make sure to set proper
permissions to the docker user by running `sudo chmod -R 777 /opt/sosrepair/sosrepair`.
* If the `PATH` and `PYTHONPATH` are not properly set run the followings:
```
    export PYTHONPATH="/opt/sosrepair/bindings:${PYTHONPATH}"
    export CPATH=":/opt/sosrepair/include"
    export PATH="/opt/sosrepair/bin:$PATH"
```
* Edit the `settings.py` file to match the bug you are running on.

