#!/bin/bash

# list of outputs to check
outputs=(output dump)

# tml executable to test against
#tml=../build-Release/tml
tml=../tml

usage() {
	echo "usage: ./tests_runner.sh <dir> [--save]" && exit 1
}

[[ -z "$1" ]] && usage
[[ ! -f ./tests_runner.sh ]] && usage
[[ ! -f $tml ]] && echo "tml executable '$tml' not found" && exit 1

dir="$1"
shift
dir_expected="$1/expected"
save=false
[[ "$1" == "--save" ]] && echo "saving" && save=true && shift
flags="$@"
status=0

# saves output ($1) as expected ($2)
save_output() {
	[[ -s "$1" ]] \
		&& cat "$1" > "$2" \
		|| rm -f "$2"
}

# return true if files not same
check_expected_failed() {
	cmp --silent "$1" "$2" && return 1 || return 0
}

# checks output ($1) if it's same as expected ($2)
check_output() {
	[[ -s "$1" ]] && [[ -f "$2" ]] \
		&& check_expected_failed "$1" "$2" && return 1
	return 0
}

# cleans output ($2) of executed program ($1)
clean_output() {
	rm -f "$1.$2"
}

# runs program ($1) and redirect outputs into files
run() {
	options=(-i "$1" -no-optimize -no-info -no-benchmarks -no-debug $flags)
	##if [[ $save == true ]]
	##then
	##	options+=(${@:2})
	##else
	##	options+=(${@:1})
	##fi
	for output in ${outputs[*]}; do
		options+=("--$output" "$1.$output")
	done
	$tml "${options[@]}"
}

# save outputs of program ($1) as expected
save() {
	filename="$(basename -- "$1")"
	mkdir -p "$dir_expected"
	for output in ${outputs[*]}; do
		save_output "$1.$output" "$dir_expected/$filename.$output"
	done
	echo "saved"
}

# checks outputs of executed program ($1) if they're same as expected
check() {
	filename="$(basename -- "$1")"
	for output in ${outputs[*]}; do
		check_output "$1.$output" "$dir_expected/$filename.$output" \
			|| return 1
	done
	return 0
}

# cleans outputs of program ($1)
clean() {
	for output in ${outputs[*]}; do
		clean_output "$1" "$output"
	done
}

# run tests
for P in $dir/*.tml; do
	echo -ne "$P: \t"
	run "$P"
	[[ $save == true ]] \
		&& save "$P" \
		|| ( check "$P" \
			&& echo "ok" \
			|| ( echo "fail" && status=1 ) )
	clean "$P"
done

exit $status
