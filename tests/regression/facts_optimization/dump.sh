#!/bin/bash

DIR=$1
EXECUTABLE=$2

#rm $TABLE

for file in $(ls $DIR/*.tml)
do
	$2 -i $file >> expected/$file.dump
done
