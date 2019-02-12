g++ tcgen.cpp
./a.out $1 > $1
cd ..
g++ -std=c++1y tml.cpp -W -Wall -Wpedantic -otml -O3 -flto
cd -
time ../tml < $1 | sort > r
g++ tcres.cpp
./a.out $1 | sort > t
rm a.out
diff -w r t
