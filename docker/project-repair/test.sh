#!/bin/sh
MAINDIR=`dirname $0`
TESTDIR=/opt/project-db/IntroClass/median/tests/blackbox
ulimit -t 2
cd $MAINDIR
rm -rf $1.out
(./median.o < $TESTDIR/$1.in >> $1.out  2>&1; (diff --ignore-all-space $1.out $TESTDIR/$1.out && (echo "PASS")) || (echo "FAIL")) &
wait
exit 0
