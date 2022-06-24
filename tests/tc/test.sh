[[ -z "$1" ]] && echo "use number of vertices as argument" && exit 1
g++ tcgen.cpp # compile a program that outputs a tml program calculating transitive closure over a circular graph with $1 vertices
./a.out $1 > $1.tml # output the tml program into a file
mkdir -p build-test && cd build-test
rm -f CMakeCache.txt
cmake ../../../src
make -j4
#g++ -std=c++1y tree.cpp transform.cpp output.cpp bdd.cpp dict.cpp driver.cpp input.cpp lp.cpp main.cpp query.cpp rule.cpp -W -Wall -Wpedantic -otml -O3 -flto # compile tml with optimization flags
cd -
/usr/bin/time -v ./build-test/tml < $1.tml > r # run tml, sort the output and save it into file "r"
sort r > r1
g++ tcres.cpp # compile a program that prints the desired result
./a.out $1 | sort > t # run it and output into file "t"
rm a.out # cleanup
rm -rf build-test
diff -w r1 t # diff files "r" and "t"
rm $1.tml r r1 t
