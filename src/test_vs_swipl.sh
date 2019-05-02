#/bin/bash
g++ ../tests/rand_prog.cpp
DIFF=""
while [ "$DIFF" == "" ]
do
	INPUT=`./a.out`
	echo $INPUT
	./tml --swipl < $INPUT > tml.output 2> tml.fname
	OUTPUT=`head -n 1 tml.fname | awk 'NF>1{print $NF}'`
	echo $OUTPUT
	timeout 5 swipl $OUTPUT > swipl.output 2> /dev/null
	if [ $? -eq 124 ]; then
		DIFF=""
	else
		sed -i 's/,/ /g' swipl.output
		sed -i 's/$/./g' swipl.output
		sort swipl.output > swipl.sorted
		sort tml.output > tml.sorted
		DIFF=$(diff -B -Z swipl.sorted tml.sorted)
	fi
done
echo "diff:"
diff -B -Z swipl.sorted tml.sorted
echo "input:"
cat $INPUT
echo "tml output:"
cat tml.sorted
