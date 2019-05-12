cmake_minimum_required(VERSION 3.1)
project(tau)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_VERBOSE_MAKEFILE true)

add_executable(tml
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
	output.cpp
	print_prolog.cpp
	save_csv.cpp
	tables.h
	tables.cpp
	token.h
	token.cpp
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
