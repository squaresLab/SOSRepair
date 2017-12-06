#!bin/bash


MY_PATH="`dirname \"$0\"`"
while read j; do
	FINE=0
	NOPOS=0
	NONEG=0
	ERR=0
	CURBUG=$j
	echo $j
	for i in $MY_PATH/Settings/$CURBUG/settings*.py; do
		echo $i
		cp -f $i $MY_PATH/settings.py
		python2.7 $MY_PATH/run.py
		res=$?
		#(( $results[$res]++ ))
		case $res in
		0*)
			((FINE++));;
		1*)
			((NOPOS++));;
		2*)
			((NONEG++));;
		3*)
			((ERR++));;
		esac
	done
	echo $CURBUG
	echo $FINE
	echo $NOPOS
	echo $NONEG
	echo $ERR
done<$MY_PATH/defectClasses.txt
