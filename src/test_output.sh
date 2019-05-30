#!/bin/bash

g++ -W -Wall -Wextra -Wpedantic -g -DDEBUG -std=gnu++17 output.test.cpp \
	&& ./a.out >test_output.stdout 2>test_output.stderr || exit

OUTPUT=`head -n 1 test_output.stdout` && [ "$OUTPUT" == "stdout test" ] \
	&& echo "output ok" || echo "output not ok"

ERRORS=`cat test_output.stderr` && \
[ "$ERRORS" == "output 'noname' targeting @name without name
stderr test" ] \
	&& echo "stderr ok" || echo "stderr not ok"

NAME1_CONTENT=`cat named.name1` && [ "$NAME1_CONTENT" == "named1 test" ] \
	&& echo "name1 ok" || echo "name1 not ok"

NAME2_CONTENT=`cat named.name2` && [ "$NAME2_CONTENT" == "named2 test" ] \
	&& echo "name2 ok" || echo "name2 not ok"

FILE_CONTENT=`cat test.file`
[ "$FILE_CONTENT" == "file test" ] \
	&& echo "file ok" || echo "file not ok"

echo && echo "STDERR:" && cat test_output.stderr
echo && echo "STDOUT:" && cat test_output.stdout

rm a.out test_output.stdout test_output.stderr named.name1 named.name2 test.file
