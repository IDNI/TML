cmake_minimum_required(VERSION 3.13)
set(CMAKE_VERBOSE_MAKEFILE true)

project(tml)

if(CMAKE_CONFIGURATION_TYPES)
	set(CMAKE_CONFIGURATION_TYPES Debug Release PgoScan PgoRun)
	set(CMAKE_CONFIGURATION_TYPES
		"${CMAKE_CONFIGURATION_TYPES}" CACHE STRING "" FORCE
	)
endif()

set(TML_DIR "${CMAKE_CURRENT_SOURCE_DIR}/..")
list(APPEND CMAKE_MODULE_PATH ${TML_DIR}/cmake)
include(tml-common)

set(TML_HEADERS
	TML.h
	bdd.h
	defs.h
	dict.h
	driver.h
	err.h
	input.h
	options.h
	output.h
	repl.h
	tables.h
)

set(TML_SOURCES
	proof.cpp
	bdd.cpp
	bdd_ext.cpp
	binary.cpp
	dict.cpp
	driver.cpp
	input.cpp
	options.cpp
	output.cpp
	print_prolog.cpp
	print_souffle.cpp
	repl.cpp
	save_csv.cpp
	tables.cpp
	tables_ext.cpp
	transform.cpp
)

set(TML_DEBUG_OPTIONS "-O0;-DDEBUG;-ggdb3")
set(TML_RELEASE_OPTIONS "-O3;-DNDEBUG")

set(TML_PGO_DIR "${PROJECT_BINARY_DIR}/pgo")
set(TML_PGO_OPTIONS
	"$<IF:$<OR:$<CONFIG:PgoScan>,$<CONFIG:PgoRun>>,-fprofile-dir=${TML_PGO_DIR},>"
	"$<$<CONFIG:PgoScan>:-fprofile-generate=${TML_PGO_DIR}>"
	"$<$<CONFIG:PgoRun>:-fprofile-use=${TML_PGO_DIR}>"
)

set(TML_COMPILE_OPTIONS
	"$<IF:$<CONFIG:Debug>,${TML_DEBUG_OPTIONS},${TML_RELEASE_OPTIONS}>"
	"$<$<CONFIG:Release>:-flto>"
	${TML_PGO_OPTIONS}
)
set(TML_LINK_OPTIONS ${TML_PGO_OPTIONS})


# object library
#################

add_library(TMLo OBJECT)
target_setup(TMLo)
target_compile_options(TMLo     PRIVATE ${TML_COMPILE_OPTIONS} -fPIC)
target_link_options(TMLo        PRIVATE ${TML_LINK_OPTIONS})
target_sources(TMLo             PRIVATE ${TML_SOURCES} ${TML_HEADERS})
target_include_directories(TMLo PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
)


# shared library
#################

add_library(TMLso SHARED)
add_library(TML::TMLso ALIAS TMLso)
target_setup(TMLso)
target_compile_options(TMLso     PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(TMLso        PRIVATE ${TML_LINK_OPTIONS})
target_link_libraries(TMLso      TMLo)
target_include_directories(TMLso PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
	$<INSTALL_INTERFACE:.>
)
set_target_properties(TMLso PROPERTIES
	EXPORT_NAME TMLso
	PUBLIC_HEADER "${TML_HEADERS}"
)


# static library
#################

add_library(TMLs STATIC)
add_library(TML::TMLs ALIAS TMLs)
target_setup(TMLs)
target_compile_options(TMLs     PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(TMLs        PRIVATE ${TML_LINK_OPTIONS})
target_link_libraries(TMLs      TMLo)
target_include_directories(TMLs PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
)
set_target_properties(TMLs PROPERTIES OUTPUT_NAME "TML")


# executable
#############

add_executable(tml)
target_setup(tml)
target_compile_options(tml PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(tml    PRIVATE ${TML_LINK_OPTIONS})
target_sources(tml         PRIVATE main.cpp)
target_link_libraries(tml  TMLs)


# executable using shared library
##################################

add_executable(tml_shared)
target_setup(tml_shared)
target_compile_options(tml_shared PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(tml_shared    PRIVATE ${TML_LINK_OPTIONS})
target_sources(tml_shared         PRIVATE main.cpp)
target_link_libraries(tml_shared  TMLso)
exclude(tml_shared)


# install
##########

include(GNUInstallDirs)
install(TARGETS tml TMLso TMLo
	EXPORT TML
	LIBRARY       DESTINATION ${CMAKE_INSTALL_LIBDIR}
	PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/TML
	RUNTIME       DESTINATION ${CMAKE_INSTALL_BINDIR}
)
export(EXPORT TML FILE ${TML_DIR}/tml-config.cmake)
install(EXPORT TML DESTINATION ${PROJECT_BINARY_DIR})
