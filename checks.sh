#!/bin/bash

BUILD_TYPE="Debug"
SUFFIX="Debug"
BUILD_DIR="build-${SUFFIX}"
CMAKE_OPTIONS="-DBUILD_CPPCHECK=TRUE -DBUILD_CLANG_TIDY=TRUE -DCMAKE_CXX_COMPILER=clang++ ${@:3}"

./build.sh Debug $CMAKE_OPTIONS

cd "${BUILD_DIR}"
NINJA_BIN="$(which ninja 2>&1)";
if [ -z $NINJA_BIN ]; then
  make -j5 cppcheck
  make -j5 clang-tidy
  make -j5 tml-check
else
  ninja cppcheck
  ninja clang-tidy
  ninja tml-check
fi
