#!/bin/bash

#rm -f ./test_file*
ret=1
g++ 2cnf_extraction_test.cpp \
	../cmake-build-debug/libTML.a \
	-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
	-DWITH_THREADS=TRUE \
	-std=c++17 -O0 -DDEBUG -ggdb3 -oarchive.test -lgcov \
					&& ./archive.test

ret=$?
#hexdump -Cv ./test_file1.bin > ./test_file1.bin.hexdump
rm -f ./archive.test ./test_file* ./archive.test.debug
exit $ret
