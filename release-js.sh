#!/bin/bash

./build.sh Release -DBUILD_JSLIB=1 -DBUILD_JSMODULE=1 $@
cp js/test.html js/tmljs build-Release/
