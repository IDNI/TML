#!/bin/bash

rm -f output.test output.test.stdout output.test.stderr named.name1 named.name2 test.file
ret=0

sources=(utils.cpp dict.cpp input.cpp tables.cpp tables_builtins.cpp
	tables_ext.cpp form.cpp builtins.cpp bdd.cpp bdd_ext.cpp analysis.cpp
	options.cpp)
objects=(utils.o dict.o input.o tables.o tables_builtins.o tables_ext.o
	bdd.o bdd_ext.o form.o builtins.o analysis.o options.o)

#[[ -f tml.o ]] || \
(
	for S in "${sources[@]}"
	do
		# echo "$S"
		g++ -c "../src/$S" \
			-W -Wall -Wextra -Wpedantic \
			-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
			-std=c++17 -O0 -DDEBUG -ggdb3
	done
	echo ${objects[@]} | xargs ld -o tml.o -relocatable # ld -relocatable
	echo ${objects[@]} | xargs rm -f
)

g++ output.test.cpp tml.o ../src/output.cpp \
	-W -Wall -Wextra -Wpedantic \
	-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
	-std=c++17 -O0 -DDEBUG -ggdb3 -ooutput.test \
		&& ./output.test >output.test.stdout 2>output.test.stderr \
		|| ( echo "output: failed"; ret=1 )

# echo STDOUT
# cat output.test.stdout
# echo STDERR
# cat output.test.stderr

cat output.test.info

check_file_fail=0

check_file_content() {
	OUTPUT=`head -n 1 $1` && [ "$OUTPUT" == "$2" ] \
	|| ( echo "output: '$1' does not match '$2'"; check_file_fail=1 )
}

check_file_content output.test.stdout "stdout test"
check_file_content output.test.stderr "stderr test"

rm -f output.test output.test.stdout output.test.stderr \
	output.test.file* output.test.info named.name1 named.name2

echo -n "output: check files "
[[ check_file_fail == 1 ]] && ( echo "failed."; ret=1 ) || echo "ok."
exit $ret
