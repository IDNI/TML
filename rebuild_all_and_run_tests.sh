#!/bin/bash

DIR=$(pwd)
rm -rf ./build-Debug ./build-Release
./build.sh Debug $@
./build.sh Release $@
./build-Release/tests/test_tml
cd tests
for dir in `find ./regression -maxdepth 1 -type d -not -name "expected"`; do
	./tests_runner.sh $dir
done
./unit_tests_runner.sh $@
cd $DIR
