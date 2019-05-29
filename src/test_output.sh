#!/bin/bash

g++ output.test.cpp -DDEBUG && ./a.out >test_output.stdout 2>test_output.stderr

OUTPUT=`head -n 1 test_output.stdout`
[ "$OUTPUT" == "stdout test" ] && echo "output ok" || echo "output not ok"

TMP=`head -n 1 test_output.stderr | sed 's/\s.*//g'`
TMP_CONTENT=`cat $TMP`
[ "$TMP_CONTENT" == "tmp test" ] && echo "tmp ok" || echo "tmp not ok"

NONAMED=`head -n 2 test_output.stderr | tail -n 1 | sed 's/\s.*//g'`
NONAMED_CONTENT=`cat $NONAMED`
[ "$NONAMED_CONTENT" == "noname test" ] && echo "noname ok" || echo "noname not ok"

NAME1_CONTENT=`cat named.name1`
[ "$NAME1_CONTENT" == "named1 test" ] && echo "name1 ok" || echo "name1 not ok"

NAME2_CONTENT=`cat named.name2`
[ "$NAME2_CONTENT" == "named2 test" ] && echo "name2 ok" || echo "name2 not ok"

FILE_CONTENT=`cat test.file`
[ "$FILE_CONTENT" == "file test" ] && echo "file ok" || echo "file not ok"

echo
cat test_output.stdout

rm a.out test_output.stdout test_output.stderr named.name1 named.name2 \
	test.file $TMP $NONAMED
