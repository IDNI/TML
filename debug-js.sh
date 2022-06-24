#!/bin/bash

./build.sh Debug -DBUILD_JSLIB=1 -DEMSCRIPTEN_DIR="$(pwd)/emsdk/upstream/emscripten" $@
cp js/test.html js/tmljs build-Debug/
