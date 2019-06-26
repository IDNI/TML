cmake_minimum_required(VERSION 3.1)
project(tau)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_VERBOSE_MAKEFILE true)

add_executable(tml
	ast.h
	ast.cpp
	bdd.cpp
	bdd.h
	defs.h
	dict.h
	dict.cpp
	driver.cpp
	driver.h
	input.cpp
	input.h
	main.cpp
	options.h
	options.cpp
	output.h
	output.cpp
	print_prolog.cpp
	print_souffle.cpp
	save_csv.cpp
	tables.h
	tables.cpp
	transform.cpp
	#	tree.cpp
)

set(CMAKE_CXX_FLAGS "-W -Wall -Wextra -Wpedantic")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DDEBUG -ggdb3")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3 -flto")
set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")
if(NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif()

# populate and add GIT_DESCRIBED, GIT_BRANCH and GIT_COMMIT_HASH definitions
execute_process(
  COMMAND git describe --tags --always
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
  OUTPUT_VARIABLE GIT_DESCRIBED
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
execute_process(
  COMMAND git rev-parse --abbrev-ref HEAD
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
  OUTPUT_VARIABLE GIT_BRANCH
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
execute_process(
  COMMAND git log -1 --format=%h
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
  OUTPUT_VARIABLE GIT_COMMIT_HASH
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
add_definitions("-DGIT_DESCRIBED=L\"${GIT_DESCRIBED}\"")
add_definitions("-DGIT_COMMIT_HASH=L\"${GIT_COMMIT_HASH}\"")
add_definitions("-DGIT_BRANCH=L\"${GIT_BRANCH}\"")
