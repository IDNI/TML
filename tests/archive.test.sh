rm -f ./test_file*
ret=1
g++ archive.test.cpp \
	../build-Debug/libTML.a \
	-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
	-DWITH_THREADS=TRUE \
	-std=c++17 -O0 -DDEBUG -ggdb3 -oarchive.test -lgcov \
					&& ./archive.test

ret=$?
#hexdump -Cv ./test_file1.bin
rm -f ./archive.test ./test_file* ./archive.test.debug
exit $ret
