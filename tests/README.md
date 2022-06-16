# Testing

## Unit testing

Doctest unit tests are built in the build directory.
From the build directory you can run `../tests/run_unit_tests.sh` to execute
them.

## Regression testing

There are several scripts useful for regression testing.
These tests should be executed in this (tests) directory.

`./run_regression_tests.sh <dir>`
	- executes tests from a directory and compares output with content in
	a subdirectory expected
	Example: `./run_regression_tests.sh ./regression/intro`
	or `./run_regression_tests.sh ./regression/quantifiers`

`./run_nodejs_regression_tests.sh <dir>`
	- executes tests from a directory using tmljs (NodeJS)

`./run_regression_tests_with.sh <tml> <dir>`
	- executes test with a provided executable as a first argument

`./run_all_regression_tests.sh`
	- executes all tests from directory `regression`

`./run_all_nodejs_regression_tests.sh`
	- same as above but using tmljs (NodeJS)

If a test directory contains a file named `options`, content of the file is used
as additional command line options passed to the TML binary (see for example
./regression/nested_progs/options)

To save tests' outputs as expected after adding or changing a test program
append the `--save` argument to the command. Be sure your programs are working
fine before storing their outputs as expected.

Example: `./run_regression_tests.sh ./regression --save`
