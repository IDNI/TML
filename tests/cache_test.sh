#!/bin/bash

rm -f ./cache_test
ret=0

g++ cache_test.cpp \
	../build-Release/libTML.a \
	-W -Wall -Wextra -Wpedantic \
	-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
	-DWITH_THREADS=TRUE \
	-std=c++17 -O0 -DDEBUG -ggdb3 -ocache_test -lgcov \
					&& ./cache_test

ret=$?
rm -f ./cache_test
exit $ret
