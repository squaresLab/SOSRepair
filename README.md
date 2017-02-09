# SearchRepair #

SearchRepair is an automatic program repair tool which tries to fix programs with the help of both generate-and-validate
and semantics-based techniques.

### Requirements ###

* KLEE
You need to have KLEE up and running in your system. Find the instruction of how to install KLEE on your system [here](http://klee.github.io/build-llvm34/)
* llvm and clang
You need to install llvm and clang by source to be able to modify and extend it later. [Instruction](http://llvm.org/docs/GettingStarted.html)
* Postgres
We will use Postgres as our database. Make sure you also install it's python binding (psycopg). You can
 install it using pip.
* Z3 SMT solver
You can install it from [here](https://github.com/Z3Prover/z3).

### Set-up ###

* You need to apply the clang_patch file to clang that you cloned from the source and build it. TODO 
* You probably need to set your PYTHONPATH to include clang python binding. 
* Create a database on postgres.
* Edit settings.py file and edit based on your settings. It's mostly possible to understand what the configs are just by
looking at their names but I'll try to add comments.


### Running ###

* If you need to generate database go to file 'run.py' and at the end of file edit the call to 'main()' to 'main(True)'
otherwise just leave it te way it is.
* If you want to remove logs from previous runs delete 'logs/repair.log'.
* Run "python2.7 run.py"
* Whenever tool finds a patch it will stop since the default value for ALL_PATCHES in settings file is False but if
 you want it to find all the patches change that setting and you'll find all the patches at folder 'patches'.

