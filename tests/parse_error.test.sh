#!/bin/bash

rm -f ./parse_error.test
ret=1
g++ parse_error.test.cpp \
	../build-Debug/libTML.a \
	-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
	-DWITH_THREADS=TRUE $@ \
	-std=c++17 -O0 -DDEBUG -ggdb3 -oparse_error.test -lgcov \
					&& ./parse_error.test
ret=$?
rm -f ./parse_error.test
exit $ret
