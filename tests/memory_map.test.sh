#!/bin/bash

rm -f ./test_file*.mmap
ret=1
g++ memory_map.test.cpp \
	../build-Debug/libTML.a \
	-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
	-std=c++17 -O0 -DDEBUG -ggdb3 -omemory_map.test -lgcov \
					&& ./memory_map.test
ret=$?
rm -f ./memory_map.test ./test_file*.mmap
exit $ret
