#!/bin/bash

TMLG="./src/tml.g"
TMLGCPP="$TMLG.cpp"

# backup tml.g.cpp
if [[ -e $TMLG ]] ; then
	NAME="$TMLGCPP.bak"
	if [[ -e $NAME || -L $NAME ]] ; then
	    i=0
	    while [[ -e $NAME$i || -L $NAME$i ]] ; do
	        let i++
	    done
	    NAME="$NAME$i"
	fi
	mv "$TMLGCPP" "$NAME"
fi

# generate tml.g.cpp from tml.g
./build-Release/tml -i $TMLG -cpp $TMLGCPP --dont-run
