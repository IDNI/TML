#!/bin/bash

rm -f ./canonicity_test
ret=0

g++ canonicity_test.cpp \
	../../build-Release/libTML.a \
	-W -Wall -Wextra -Wpedantic \
	-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
	-DWITH_THREADS=TRUE \
	-std=c++17 -O0 -DDEBUG -ggdb3 -ocanonicity_test -lgcov \
					&& ./canonicity_test

ret=$?
rm -f ./canonicity_test
exit $ret
