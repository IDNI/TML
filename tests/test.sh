g++ tcgen.cpp # compile a program that outputs a tml program calculating transitive closure over a circular graph with $1 vertices
./a.out $1 > $1 # output the tml program into a file
cd ..
g++ -std=c++1y tml.cpp driver.cpp bdd.cpp -W -Wall -Wpedantic -otml -O3 -flto # compile tml with optimization flags
cd -
/usr/bin/time -v ../tml < $1 | sort > r # run tml, sort the output and save it into file "r"
g++ tcres.cpp # compile a program that prints the desired result
./a.out $1 | sort > t # run it and output into file "t"
rm a.out # cleanup
diff -w r t # diff files "r" and "t"
