cmake_minimum_required(VERSION 3.13)
set(CMAKE_VERBOSE_MAKEFILE true)

set(TML_DIR "${CMAKE_CURRENT_SOURCE_DIR}/..")
list(APPEND CMAKE_MODULE_PATH ${TML_DIR}/cmake)
include(tml-common)

set(TML_HEADERS
	TML.h
	bdd.h
	defs.h
	dict.h
	driver.h
	input.h
	options.h
	output.h
	tables.h
)

set(TML_SOURCES
	ast.cpp
	bdd.cpp
	dict.cpp
	driver.cpp
	input.cpp
	options.cpp
	output.cpp
	print_prolog.cpp
	print_souffle.cpp
	save_csv.cpp
	tables.cpp
	transform.cpp
)

set(TML_COMPILE_OPTIONS
	"$<$<CONFIG:DEBUG>:-O0;-ggdb3;-DDEBUG>"
	"$<$<CONFIG:RELEASE>:-O3;-flto;-DNDEBUG>"
)


# shared library
#################

add_library(TML SHARED)
add_library(TML::TML ALIAS TML)
target_setup(TML)
target_compile_options(TML     PRIVATE ${TML_COMPILE_OPTIONS})
target_sources(TML             PRIVATE ${TML_SOURCES} ${TML_HEADERS})
target_include_directories(TML PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
	$<INSTALL_INTERFACE:.>
)
set_target_properties(TML PROPERTIES
	EXCLUDE_FROM_ALL 1
	EXCLUDE_FROM_DEFAULT_BUILD 1
	EXPORT_NAME TML
	PUBLIC_HEADER ${TML_HEADERS})


# static library
#################

add_library(TMLs STATIC)
target_setup(TMLs)
target_compile_options(TMLs     PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(TMLs        PRIVATE ${TML_COMPILE_OPTIONS})
target_sources(TMLs             PRIVATE ${TML_SOURCES} ${TML_HEADERS})
target_include_directories(TMLs PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
)
set_target_properties(TMLs PROPERTIES OUTPUT_NAME "TML")


# executable
#############

add_executable(tml)
target_setup(tml)
target_compile_options(tml PRIVATE ${TML_COMPILE_OPTIONS})
target_sources(tml         PRIVATE main.cpp)
target_link_libraries(tml  TMLs)


# executable using shared library
##################################

add_executable(tml_shared)
target_setup(tml_shared)
target_compile_options(tml_shared PRIVATE ${TML_COMPILE_OPTIONS})
target_sources(tml_shared         PRIVATE main.cpp)
target_link_libraries(tml_shared  TML)
set_target_properties(tml_shared  PROPERTIES
	EXCLUDE_FROM_ALL 1
	EXCLUDE_FROM_DEFAULT_BUILD 1)


# install
##########

include(GNUInstallDirs)
install(TARGETS tml TML
	EXPORT TML
	LIBRARY       DESTINATION ${CMAKE_INSTALL_LIBDIR}
	PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/TML
	RUNTIME       DESTINATION ${CMAKE_INSTALL_BINDIR}
)
export(EXPORT TML FILE ${TML_DIR}/tml-config.cmake)
install(EXPORT TML DESTINATION ${PROJECT_BINARY_DIR})
