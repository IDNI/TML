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

NINJA_BIN="$(which ninja 2>&1)";
if [ $? -ne 0 ]; then
    NINJA_BIN="$(which ninja-build 2>&1)";
    if [ $? -ne 0 ]; then
        NINJA_BIN="";
    fi
fi

if [ -z $NINJA_BIN ]; then
  echo "Using make build system"
  cmake .. -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" ${@:2}
  cmake --build . -- -j5
else
  echo "Using Ninja build system"
  cmake .. -G Ninja -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" ${@:2}
  ninja
fi

cd ..
