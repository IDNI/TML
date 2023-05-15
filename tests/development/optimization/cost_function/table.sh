#!/bin/bash

DIR=$1
EXECUTABLE=$2
TABLE=$3

rm $TABLE

for file in $(ls $DIR/*.tml)
do
    echo -n "FILE: ">> $TABLE
    echo  $file >> $TABLE
    /usr/bin/time -a -h -o $TABLE $2 -i $file >> $TABLE
done
