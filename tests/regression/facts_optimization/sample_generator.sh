#!/bin/bash

FACT=$1
LINES=$2
ARGS=$3
FILE=$4

rm $4

for (( i=0; i<$LINES; i++)) 
do
    echo -n "$FACT(" >> $FILE
    for (( j=0; j<$ARGS; j++)) 
    do
        echo -n "$(($RANDOM)) " >> $FILE
    done
    echo ")." >> $FILE
done


