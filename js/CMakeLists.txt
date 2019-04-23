cmake_minimum_required(VERSION 3.1)
project(tml.js)

set(CMAKE_CXX_COMPILER em++)
set(CMAKE_CXX_FLAGS "-W -Wall -Wextra -Wpedantic -s EXIT_RUNTIME=1")
set(CMAKE_CXX_FLAGS_DEBUG "-O0 -DDEBUG -g4")
set(CMAKE_CXX_FLAGS_RELEASE "-O0 -DNDEBUG -g0 --js-opts 1")
set(CMAKE_CXX_LINK_FLAGS "--post-js glue.js")

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_VERBOSE_MAKEFILE true)

add_executable(tml.js
	tml.cpp
	../src/bdd.cpp
	../src/bdd.h
	../src/defs.h
	../src/dict.h
	../src/dict.cpp
	../src/driver.cpp
	../src/driver.h
	../src/input.cpp
	../src/input.h
	../src/lp.cpp
	../src/lp.h
	../src/query.cpp
	../src/query.h
	../src/rule.cpp
	../src/rule.h
	../src/term.h
	../src/transform.cpp
	../src/output.cpp
	../src/tree.cpp
	../src/print_xsb.cpp
	../src/print_souffle.cpp
	../src/save_csv.cpp)

if(NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif()
