#!/bin/bash

DIR=$(pwd)
rm -rf ./build-Debug ./build-Release
./build.sh Debug $@
./build.sh Release $@
./build-Release/tests/test_tml
cd tests
declare -a dirs=(intro regression macro quantifiers ebnf beyondcfg)
for testdir in "${dirs[@]}"; do
	./tests_runner.sh $testdir
done
./unit_tests_runner.sh $@
cd $DIR
#./checks.sh

