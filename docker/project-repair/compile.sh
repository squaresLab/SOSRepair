#!/bin/sh
MAINDIR=`dirname $0`
cd $MAINDIR
rm median.o
gcc -fprofile-arcs -ftest-coverage median.c -o median.o
exit $?
