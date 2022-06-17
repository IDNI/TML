[[ -z "$1" ]] && echo "use number of vertices as the first argument" && exit 1
[[ -z "$2" ]] && echo "use number of edges as the second argument" && exit 1
g++ tcrand.cpp -O3 -flto
echo "gen:"
/usr/bin/time -v ./a.out $1 $2 in out
mkdir -p build-test && cd build-test
rm -f CMakeCache.txt
cmake ../../../src
make -j4
cd -
echo "tml:"
/usr/bin/time -v ./build-test/tml < in > r
sort r > r1
sort out > r2
rm a.out
diff -w r1 r2
rm r r1 r2 in out
