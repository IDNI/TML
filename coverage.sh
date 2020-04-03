#!/bin/bash

BUILD_TYPE="Debug"
SUFFIX="Debug"
BUILD_DIR="build-${SUFFIX}"
CMAKE_OPTIONS="-DBUILD_CODE_COVERAGE=TRUE ${@:3}"

mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"
rm -f ./CMakeCache.txt

cmake .. -G "Unix Makefiles" -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" ${CMAKE_OPTIONS} &&
make -j5 &&
make -j5 doctest_coverage_html
echo -e "\033[0;34mTo generate XML report run \033[1;47mmake doctest_coverage\033[0;34m from ./build-Debug directory\033[0m"