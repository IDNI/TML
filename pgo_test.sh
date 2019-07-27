#!/bin/bash

# command to be used for scanning and measuring PGO
# (--info and --error set to @stdout keeps stderr for benchmark results only)
DEFAULT_COMMAND="./tml --bin --info @stdout --error @stdout < tml.g"

# or pass command as a first argument string
COMMAND="${1:-${DEFAULT_COMMAND}}"

function benchmark {
	/usr/bin/time -f '[user]=%U [system]=%S [cpu]=%P [mem]=%M' $@
}

# $1 = BUILD_TYPE (Release, PgoScan or PgoRun)
function build_and_run {
	DIR=$(pwd)
	./build.sh $1 && cd build-Release && \
	eval "benchmark $COMMAND 2> ./pgo.stats/$1.txt"
	cd $DIR
}

function initialize {
	mkdir -p ./build-Release/pgo.stats && \
	rm -f ./build-Release/pgo.stats/*.txt && \
	cp src/tml.g build-Release/
}

function run_tests {
	for RUN in {Release,PgoScan,PgoRun};
	do
		build_and_run $RUN
	done && rm -rf ./build-Release/pgo
}

function print_results {
	echo && echo "PGO test results of: '$COMMAND'" && echo && \
	for RUN in {Release,PgoRun};
	do
		echo -n "$RUN:" && cat "./build-Release/pgo.stats/$RUN.txt"
	done && echo
}

initialize && run_tests && print_results
