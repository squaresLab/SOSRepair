#!/bin/sh
MAINDIR=`dirname $0`
ulimit -t 2
cd $MAINDIR
rm -rf my.t1 my.t2 my.t3 my.t4 my.t5 my.t7
($1 < t1 >> my.t1  2>&1; (diff output.t1 my.t1 && (echo "+< $MAINDIR/t1" >> $2)) || (echo "-< $MAINDIR/t1" >> $2)) &
($1 < t2 >> my.t2  2>&1; (diff output.t2 my.t2 && (echo "+< $MAINDIR/t2" >> $2)) || (echo "-< $MAINDIR/t2" >> $2)) &
($1 < t3 >> my.t3  2>&1; (diff output.t3 my.t3 && (echo "+< $MAINDIR/t3" >> $2)) || (echo "-< $MAINDIR/t3" >> $2)) &
($1 < t4 >> my.t4  2>&1; (diff output.t4 my.t4 && (echo "+< $MAINDIR/t4" >> $2)) || (echo "-< $MAINDIR/t4" >> $2)) &
($1 < t5 >> my.t5  2>&1; (diff output.t5 my.t5 && (echo "+< $MAINDIR/t5" >> $2)) || (echo "-< $MAINDIR/t5" >> $2)) &
($1 < t7 >> my.t7  2>&1 && (echo "+< $MAINDIR/t7" >> $2)) || (echo "-< $MAINDIR/t7" >> $2) &
wait
exit 0
