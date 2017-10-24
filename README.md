# SearchRepair #

SearchRepair is an automatic program repair tool which tries to fix programs with the help of both generate-and-validate
and semantics-based techniques.

### Requirements ###

* KLEE - You need to have KLEE up and running in your system. Find the
instruction of how to install KLEE on your system [here](http://klee.github.io/build-llvm34/).
SR has been confirmed to work on KLEE version 1.2 on using llvm 3.
* llvm and clang - You need to install llvm and clang by source to be
able to modify and extend it later. [Instruction](http://llvm.org/docs/GettingStarted.html).
SR has been confirmed to work on llvm commit (db55668) and clang commit (2a0e7716).
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
There is a detailed documentation on what each setting in that file is
responsible for.


### Running ###

* If you need to generate database go to file `run.py` and at the end of file edit the call to `main()` to `main(True)`
otherwise just leave it te way it is
* If you wish to remove logs from previous runs delete `logs/repair.log`.
* Run `python2.7 run.py`
* Whenever tool finds a patch it will put the patch inside folder `patches`
that is created at runtime

