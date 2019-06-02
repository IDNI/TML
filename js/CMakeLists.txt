cmake_minimum_required(VERSION 3.1)
project(tml.js)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_VERBOSE_MAKEFILE true)

add_executable(tml.js
	../src/ast.h
	../src/ast.cpp
	../src/bdd.cpp
	../src/bdd.h
	../src/defs.h
	../src/dict.h
	../src/dict.cpp
	../src/driver.cpp
	../src/driver.h
	../src/input.cpp
	../src/input.h
	../src/options.h
	../src/options.cpp
	../src/output.h
	../src/output.cpp
	../src/print_prolog.cpp
	../src/print_souffle.cpp
	../src/save_csv.cpp
	../src/tables.h
	../src/tables.cpp
	../src/transform.cpp
)

set(CMAKE_CXX_COMPILER em++)
set(CMAKE_CXX_FLAGS "-W -Wall -Wextra -Wpedantic --bind -s WASM=1 -s EXIT_RUNTIME=1 -s WARN_UNALIGNED=1 -s MODULARIZE_INSTANCE=1 -s EXPORT_NAME='tml'")
set(CMAKE_CXX_FLAGS_DEBUG "-O0 -DDEBUG -g4")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG -g0")
if(NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif()
