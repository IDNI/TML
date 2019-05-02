#/bin/bash
g++ ../tests/rand_prog.cpp
INPUT=`./a.out`
echo $INPUT
./tml --swipl < $INPUT > tml.output 2> tml.fname
OUTPUT=`head -n 1 tml.fname | awk 'NF>1{print $NF}'`
echo $OUTPUT
swipl OUTPUT > swipl.output1
cat swipl.output1 | sed -i 's/;/ /' swipl.output2
diff swipl.output2 tml.output
