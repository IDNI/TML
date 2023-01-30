set(CMAKE_VERBOSE_MAKEFILE ON)
cmake_minimum_required(VERSION 3.6 FATAL_ERROR)
list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_LIST_DIR}/cmake)

if(BUILD_JSLIB)
	set(EMSCRIPTEN_CMAKE "${EMSCRIPTEN_DIR}/cmake/Modules/Platform/Emscripten.cmake")
	if(EXISTS "${EMSCRIPTEN_CMAKE}")
		set(EMSCRIPTEN_ROOT_PATH "${EMSCRIPTEN_DIR}")
		set(CMAKE_TOOLCHAIN_FILE "${EMSCRIPTEN_CMAKE}" CACHE STRING "")
	else()
		message(SEND_ERROR "emscripten not found in '${EMSCRIPTEN_DIR}'. Use -DEMSCRIPTEN_DIR=<emscripten_install_directory>.")
	endif()
endif()

set(namespace "idni")
set(PROJECT_SHORT_NAME tml)
project("${namespace}_${PROJECT_SHORT_NAME}"
	VERSION 0.0.1
	DESCRIPTION "TML - Tau Meta Language"
)

################################################################################
option(WITH_Z3 "use Z3" FALSE)
option(WITH_THREADS "use Threads" FALSE)
option(WITH_BOOST "use Boost" FALSE)
option(WITH_WCHAR "use wchar_t for system calls (instead of char)" FALSE)
option(WITH_EXCEPTIONS "use exceptions" FALSE)
option(BUILD_SHARED_LIBRARY "Build shared library" FALSE)
option(BUILD_STATIC_LIBRARY "Build static library" FALSE)
option(BUILD_EXECUTABLE "Build executable" FALSE)
option(BUILD_SHARED_EXECUTABLE "Build executable using shared library" FALSE)
option(BUILD_TESTS "Build tests of TML" FALSE)
option(BUILD_JSLIB "Build JS version of TML library" FALSE)
option(BUILD_CLANG_TIDY "Run clang tidy" FALSE)
option(BUILD_CLANG_FORMAT "Run clang format" FALSE)
option(BUILD_CPPCHECK "Run cppcheck" FALSE)
option(BUILD_CODE_COVERAGE "Generate code coverage" FALSE)
option(BUILD_TML_CHECK "Build TML parsing check" FALSE)

if(BUILD_JSLIB)
	set(BUILD_STATIC_LIBRARY FALSE)
	set(BUILD_SHARED_LIBRARY FALSE)
	set(BUILD_EXECUTABLE FALSE)
	set(BUILD_SHARED_EXECUTABLE FALSE)
	set(BUILD_TESTS FALSE)
	set(BUILD_CODE_COVERAGE FALSE)
endif()
if(NOT BUILD_STATIC_LIBRARY)
	if(NOT BUILD_SHARED_LIBRARY)
		if(NOT BUILD_SHARED_EXECUTABLE)
			if(NOT BUILD_TESTS)
				if(NOT BUILD_JSLIB)
					if(NOT BUILD_EXECUTABLE)
						set(BUILD_EXECUTABLE TRUE)
					endif()
				endif()
			endif()
		endif()
	endif()
endif()
################################################################################
message(STATUS "EMSCRIPTEN: ${EMSCRIPTEN}")
message(STATUS "WITH_Z3: ${WITH_Z3}")
message(STATUS "WITH_THREADS: ${WITH_THREADS}")
message(STATUS "WITH_BOOST: ${WITH_BOOST}")
message(STATUS "WITH_WCHAR: ${WITH_WCHAR}")
message(STATUS "WITH_EXCEPTIONS: ${WITH_EXCEPTIONS}")
message(STATUS "BUILD_SHARED_LIBRARY: ${BUILD_SHARED_LIBRARY}")
message(STATUS "BUILD_STATIC_LIBRARY: ${BUILD_STATIC_LIBRARY}")
message(STATUS "BUILD_EXECUTABLE: ${BUILD_EXECUTABLE}")
message(STATUS "BUILD_SHARED_EXECUTABLE: ${BUILD_SHARED_EXECUTABLE}")
message(STATUS "BUILD_TESTS: ${BUILD_TESTS}")
message(STATUS "BUILD_JSLIB: ${BUILD_JSLIB}")
message(STATUS "BUILD_CLANG_TIDY: ${BUILD_CLANG_TIDY}")
message(STATUS "BUILD_CLANG_FORMAT: ${BUILD_CLANG_FORMAT}")
message(STATUS "BUILD_CPPCHECK: ${BUILD_CPPCHECK}")
message(STATUS "BUILD_CODE_COVERAGE: ${BUILD_CODE_COVERAGE}")
message(STATUS "BUILD_TML_CHECK: ${BUILD_TML_CHECK}")
################################################################################

set(PROJECT_HEADERS
	src/builtins.h
	src/cpp_gen.h
	src/defs.h
	src/dict.h
	src/driver.h
	src/err.h
	src/fof.h
	src/form.h
	src/input.h
	src/ir_builder.h
	src/options.h
	src/output.h
	src/printing.h
	src/tables.h
	src/tables_progress.h
	src/typemanager.h
)

set(PROJECT_SOURCES
	src/builtins.cpp
	src/cpp_gen.cpp
	src/dict.cpp
	src/driver.cpp
	src/fof.cpp
	src/form.cpp
	src/input.cpp
	src/ir_builder.cpp
	src/options.cpp
	src/output.cpp
	src/printing.cpp
	src/proof.cpp
	src/save_csv.cpp
	src/tables.cpp
	src/tables_progress.cpp
	src/tables_printer.cpp
	src/tables_builtins.cpp
	src/tables_ext.cpp
	src/tml_earley.cpp
	src/transform.cpp
	src/transform_guards.cpp
	src/transform_bitunv.cpp
	src/typemanager.cpp
	src/utils.cpp
)

if(WITH_THREADS)
	set(CLI_SOURCES src/main.cpp src/repl.cpp)
else()
	set(CLI_SOURCES src/main.cpp)
endif()

include(idni-common)

include(git-defs)

function(target_pass_features_on target)
	if(WITH_THREADS)
		target_compile_definitions(${target} PRIVATE "-DWITH_THREADS")
		target_link_libraries(${target} Threads::Threads)
	endif()
	if(WITH_WCHAR)
		target_compile_definitions(${target} PRIVATE "-DWITH_WCHAR")
	endif()
	if(WITH_EXCEPTIONS)
		target_compile_definitions(${target} PRIVATE "-DWITH_EXCEPTIONS")
	endif()
	target_compile_definitions(${target} PRIVATE "-DWITH_ARITH")
	target_compile_definitions(${target} PRIVATE "-DWITH_MMAP")
	target_git_definitions(${target})
endfunction()

if(NOT BUILD_JSLIB)
	include(add_git_submodule)
	set(WITH_TO_METHODS TRUE CACHE BOOL "")
	add_git_submodule(external/parser)
	set(WITH_ARITH TRUE CACHE BOOL "")
	set(WITH_MMAP TRUE CACHE BOOL "")
	add_git_submodule(external/bdd)
endif()

target_pass_features_on(${OBJECT_LIB_NAME})
target_link_libraries(${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object)
if(BUILD_JSLIB)
	exclude(${OBJECT_LIB_NAME})
endif()

if(WITH_THREADS)
	set(THREADS_PREFER_PTHREAD_FLAG ON)
	find_package(Threads)
endif()

if(WITH_BOOST)
	target_compile_definitions(${OBJECT_LIB_NAME} PRIVATE "-DWITH_BOOST")
	find_package(Boost COMPONENTS system thread REQUIRED)
	if(Boost_FOUND)
		target_include_directories(${OBJECT_LIB_NAME}
			PRIVATE ${Boost_INCLUDE_DIRS}
		)
		target_link_libraries(${OBJECT_LIB_NAME}
			Boost::boost Boost::system
		)
	endif(Boost_FOUND)
endif()

if(WITH_Z3)
	find_library(Z3 NAMES z3)
	add_library(Z3 SHARED IMPORTED)
	set_target_properties(Z3 PROPERTIES IMPORTED_LOCATION "${Z3}")
	target_link_libraries(${OBJECT_LIB_NAME} Z3)
	target_compile_definitions(${OBJECT_LIB_NAME} PRIVATE "-DWITH_Z3")
endif()

if(BUILD_STATIC_LIBRARY)
	target_pass_features_on(${STATIC_LIB_NAME})
endif()

if(BUILD_SHARED_LIBRARY)
	target_pass_features_on(${SHARED_LIB_NAME})
endif()

if(BUILD_EXECUTABLE)
	add_executable(${EXECUTABLE_NAME})
	target_setup(${EXECUTABLE_NAME})
	target_pass_features_on(${EXECUTABLE_NAME})
	target_sources(${EXECUTABLE_NAME} PRIVATE ${CLI_SOURCES})
	target_compile_definitions(${EXECUTABLE_NAME}
		PRIVATE "-DWITH_ARITH" "-DWITH_MMAP"
	)
	target_link_libraries(${EXECUTABLE_NAME}
		${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object)
	target_include_directories(${EXECUTABLE_NAME} PUBLIC 
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/bdd/src>
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/parser>	
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/parser/src>)	
	if(BUILD_CODE_COVERAGE)
		target_link_libraries(${EXECUTABLE_NAME} gcov)
	endif()
endif()

if(BUILD_SHARED_EXECUTABLE)
	add_executable(${EXE_SHARED_NAME})
	target_setup(${EXE_SHARED_NAME})
	target_pass_features_on(${EXE_SHARED_NAME})
	target_sources(${EXE_SHARED_NAME} PRIVATE ${CLI_SOURCES})
	target_compile_definitions(${EXE_SHARED_NAME}
		PRIVATE "-DWITH_ARITH" "-DWITH_MMAP"
	)
	target_link_libraries(${EXE_SHARED_NAME}
		${SHARED_LIB_NAME} idni_bdd_object idni_parser_object)
	target_include_directories(${EXE_SHARED_NAME} PUBLIC 
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/bdd/src>
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/parser>	
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/parser/src>)	
	if(BUILD_CODE_COVERAGE)
		target_link_libraries(${EXE_SHARED_NAME} gcov)
	endif()
endif()

if(BUILD_TESTS)
	set(DOCTEST_HEADER "${PROJECT_SOURCE_DIR}/src/doctest.h"
		CACHE PATH "Doctest header"
	)
	if(NOT EXISTS "${DOCTEST_HEADER}")
		message(STATUS "Downloading doctest to '${PROJECT_SOURCE_DIR}'")
		find_package(Wget REQUIRED)
		execute_process(COMMAND "${WGET_EXECUTABLE}"
			https://raw.githubusercontent.com/onqtam/doctest/master/doctest/doctest.h
			-P ${PROJECT_SOURCE_DIR}/src
		)
	endif()
	add_library(doctest INTERFACE)
	target_compile_definitions(doctest INTERFACE TML_USE_DOCTEST)
	target_include_directories(doctest PUBLIC 
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/bdd/src>
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/parser>	
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/parser/src>)	
	set(TEST_FRAMEWORK doctest)
	enable_testing()
	add_subdirectory(tests)
endif()	

if(BUILD_JSLIB)
	add_subdirectory("js")
endif()

if(NOT BUILD_JSLIB)
	include(installation)
endif()

