#!/bin/bash

BUILD_TYPE="${1:-Release}"
if [ "${BUILD_TYPE}" == "Debug" ]
then
	SUFFIX="Debug"
else
	SUFFIX="Release"
fi
BUILD_DIR="build-${SUFFIX}"

mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"
rm -f ./CMakeCache.txt

cmake .. -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" ${@:2}
cmake --build . -- -j5

cd ..
