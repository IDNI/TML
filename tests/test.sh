g++ tcgen.cpp
./a.out $1 > $1
../tml < $1 | sort > r
g++ tcres.cpp
./a.out $1 | sort > t
rm a.out
diff -w r t
