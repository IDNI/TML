#!/bin/bash

# This script executes tests.
# Run this script while in a build root directory (build-Debug/build-Release...)

status=0

######################
echo "preparing tests"
######################
echo -en "a.\nb.\nc :- a, b.\n" > ./input.test.file

####################
echo "testing input"
####################
./test_input
r=$?; [[ $r != 0 ]] && status=$r

#####################
echo "testing output"
#####################
./test_output >output.test.stdout 2>output.test.stderr
r=$?; [[ $r != 0 ]] && status=$r
cat output.test.stdout
O=`cat output.test.file2` && \
	[ "$O" == "file test"   ] \
		|| echo "ERROR: file output fail" && status=1
O=`grep -v doctest output.test.stdout | head -n 1` && \
	[ "$O" == "stdout test" ] \
		|| echo "ERROR: standard output fail" && status=1
O=`cat output.test.stderr` && \
	[ "$O" == "stderr test" ] \
		|| echo "ERROR: standard error fail" && status=1

###############
echo "cleaning"
###############
rm -f \
	output.test.stdout output.test.stderr output.test.file* \
	output.test.info named.name1 named.name2 input.test.file

exit $status
