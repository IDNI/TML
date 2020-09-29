#!/bin/bash

status=0
for P in ./*.test.sh; do
	$P $@; r=$?; [[ $r != 0 ]] && status=$r
done
exit $status
