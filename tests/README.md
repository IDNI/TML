# Regression testing

Be in the `tests` directory and run: `./tests_runner.sh <dir>` to run all *.tml
files from the dir and compare its outputs with expected ones.

Example: `./tests_runner.sh ./regression`
or `./tests_runner.sh ./intro`

To save tests' outputs as expected after adding or changing a test program
append the `--save` argument to the command. Be sure your programs are working
fine before storing their outputs as expected.

Example: `./tests_runner.sh ./regression --save`
