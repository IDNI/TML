g++ tcrand.cpp -O3 -flto
echo "gen:"
/usr/bin/time -v ./a.out $1 $2 in out
cd ../src
rm CMakeCache.txt
cmake .
make -j4
cd -
echo "tml:"
/usr/bin/time -v ../src/tml < in > r
sort r > r1
sort out > r2
rm a.out
diff -w r1 r2
#rm r r1 r2 in out
