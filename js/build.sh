BUILD_TYPE=${1:Release}
EMSCRIPTEN_ROOT=$(dirname $(which emcc))

echo "generating glue.cpp and glue.js..."
python ${EMSCRIPTEN_ROOT}/tools/webidl_binder.py tml.idl glue
echo "cmake..."
rm CMakeCache.txt
cmake . -DCMAKE_BUILD_TYPE=${BUILD_TYPE}
echo "make..."
make -j5
