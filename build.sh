#!/bin/bash

BUILD_TYPE="${1:-Release}"
BUILD_DIR="build-${BUILD_TYPE}"

mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"
rm -f ./CMakeCache.txt

cmake .. -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" ${@:2}
cmake --build . -- -j5

cd ..
