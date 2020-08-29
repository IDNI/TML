@echo off
set ret=1
g++ memory_map.test.cpp	../build-Debug/libTML.a -DGIT_DESCRIBED=1 -DGIT_COMMIT_HASH=1 -DGIT_BRANCH=1 -std=c++17 -O0 -DDEBUG -ggdb3 -omemory_map.test.exe -lgcov
memory_map.test.exe
set ret=%errorlevel%
del .\memory_map.test.exe
del .\test_file*.mmap
exit %ret%
