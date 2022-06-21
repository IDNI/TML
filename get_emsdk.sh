#!/bin/bash

[ -d "emsdk" ] \
	&& echo "emsdk already cloned" \
	|| (
		git clone https://github.com/emscripten-core/emsdk.git emsdk
		cd emsdk
		git checkout 517e02f
		cd -
	)

./emsdk/emsdk install latest
./emsdk/emsdk activate latest
