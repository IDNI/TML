#!/bin/bash

./build.sh Release -DBUILD_JSLIB=1 -DEMSCRIPTEN_DIR="$(pwd)/emsdk/upstream/emscripten" $@
cp js/test.html js/tmljs build-Release/
