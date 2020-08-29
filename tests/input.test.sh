#!/bin/bash

rm -f ./input.test
ret=0

g++ input.test.cpp \
	../build-Debug/libTML.a \
	-W -Wall -Wextra -Wpedantic \
	-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
	-DWITH_THREADS=TRUE \
	-std=c++17 -O0 -DDEBUG -ggdb3 -oinput.test -lgcov \
					&& ./input.test

ret=$?
rm -f ./input.test
exit $ret
