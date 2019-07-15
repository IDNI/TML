cmake_minimum_required(VERSION 3.13)
set(CMAKE_VERBOSE_MAKEFILE true CACHE BOOL "")

################################################################################
option(BUILD_JSLIB "Build JS version of TML library" OFF)
if(BUILD_JSLIB)
	list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_LIST_DIR}/cmake)
	include(emscripten_toolchain)
	set_emscripten_toolchain()
endif()
################################################################################

project(tml)

if(BUILD_JSLIB)
	if(EMSCRIPTEN)
		add_subdirectory("js")
	endif()
else()
	add_subdirectory("src")
endif()
