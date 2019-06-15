rm CMakeCache.txt
cmake . -DCMAKE_BUILD_TYPE=${1:Release}
make -j5
