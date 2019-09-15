g++ parse_error.test.cpp \
	../build-Debug/libTML.a \
		-DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 \
		-std=c++17 -O3 -flto -oparse_error.test \
						&& ./parse_error.test

rm -f ./parse_error.test
