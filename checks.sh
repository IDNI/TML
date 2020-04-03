#!/bin/bash

BUILD_TYPE="Debug"
SUFFIX="Debug"
BUILD_DIR="build-${SUFFIX}"
CMAKE_OPTIONS="-DBUILD_CPPCHECK=TRUE -DBUILD_CLANG_TIDY=TRUE ${@:3}"

mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"
rm -f ./CMakeCache.txt

cmake .. -G "Unix Makefiles" -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" ${CMAKE_OPTIONS} &&
make -j5 &&
make -j5 cppcheck &&
make -j5 clang-tidy