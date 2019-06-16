#!/bin/bash
DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

cd $DIR/src
#make clean
(make && patchelf --set-interpreter /home/afsoon/ManyBugs/AutomatedRepairBenchmarks.c/manybugs/lighttpd/lighttpd-bug-1913-1914/src/libs/glib/lib/ld-linux-x86-64.so.2 src/lighttpd && exit 0)|| exit 1


