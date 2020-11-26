#!/bin/bash

TML=../../../build-Release/tml
RECS=${1:-1000}

for F in *.nt; do
    head -n $RECS $F | ./nt2tml | $TML > $F.tml
done
