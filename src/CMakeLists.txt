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
	#	lp.cpp
	#	lp.h
	main.cpp
	#	query.cpp
	#	query.h
	#	rule.cpp
	#	rule.h
	#	term.h
	transform.cpp
	output.cpp
	tables.h
	tables.cpp
	#	tree.cpp
	print_xsb.cpp)

#set(CMAKE_CXX_FLAGS "-W -Wall -Wextra -Wpedantic")
set(CMAKE_CXX_FLAGS "-W -Wall -Wextra")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DDEBUG -ggdb3")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3 -flto")
set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")
if(NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif()
