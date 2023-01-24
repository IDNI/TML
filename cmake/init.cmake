set(CMAKE_VERBOSE_MAKEFILE ON)
if(NOT CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME)
    message(STATUS
    	"${PROJECT_NAME} as a subproject of [${CMAKE_PROJECT_NAME}]")
else()
    message(STATUS "${PROJECT_NAME} as a top project")
endif()

cmake_host_system_information(RESULT CORE_COUNT QUERY NUMBER_OF_LOGICAL_CORES)
if(CMAKE_CONFIGURATION_TYPES)
	set(CMAKE_CONFIGURATION_TYPES Debug Release PgoScan PgoRun)
	set(CMAKE_CONFIGURATION_TYPES
		"${CMAKE_CONFIGURATION_TYPES}" CACHE STRING "" FORCE
	)
endif()
if(NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif()
message(STATUS "CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE}")
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
	message(STATUS "CMAKE_CXX_COMPILER_ID ${CMAKE_CXX_COMPILER_ID}")
	message(STATUS "CMAKE_CXX_COMPILER ${CMAKE_CXX_COMPILER}")

	if(BUILD_CLANG_TIDY AND CMAKE_CXX_COMPILER_ID MATCHES "Clang")
		include(clang-tidy)
	endif()

	if(BUILD_CLANG_FORMAT AND CMAKE_CXX_COMPILER_ID MATCHES "Clang")
		include(clang-format)
	endif()

	if(BUILD_CPPCHECK)
		message(STATUS "Including cppcheck")
		include(cppcheck)
	endif()

	if (BUILD_CODE_COVERAGE)
		find_program(GCOVR gcovr)
		if(GCOVR)
			message(STATUS "Including code coverage")
			set(CMAKE_CXX_FLAGS "-g -O0 -fprofile-arcs -ftest-coverage" CACHE STRING "Code coverage CXX options" FORCE)
			include(code-coverage)
			append_coverage_compiler_flags()
		else()
			message(WARNING "Gcovr not found!")
		endif()
	endif()

	if(BUILD_TML_CHECK)
		message(STATUS "Including tml parsing check")
		include(tml-check)
	endif()
endif()

set(CMAKE_VERBOSE_MAKEFILE true CACHE BOOL "")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(USED_CMAKE_GENERATOR
	"${CMAKE_GENERATOR}" CACHE STRING "Expose CMAKE_GENERATOR" FORCE
)
if(USED_CMAKE_GENERATOR MATCHES "Ninja")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fdiagnostics-color=always")
endif()	

set(DEBUG_OPTIONS "-O0;-DDEBUG;-ggdb3")
set(RELEASE_OPTIONS "-O3;-DNDEBUG")

set(PGO_DIR "${PROJECT_BINARY_DIR}/pgo")
set(PGO_OPTIONS
	"$<IF:$<OR:$<CONFIG:PgoScan>,$<CONFIG:PgoRun>>,-fprofile-dir=${TML_PGO_DIR},>"
	"$<$<CONFIG:PgoScan>:-fprofile-generate=${TML_PGO_DIR}>"
	"$<$<CONFIG:PgoRun>:-fprofile-use=${TML_PGO_DIR}>"
)

set(COMPILE_OPTIONS
	"$<IF:$<CONFIG:Debug>,${DEBUG_OPTIONS},${RELEASE_OPTIONS}>"
	"$<$<CONFIG:Release>:-flto=auto>"
	${PGO_OPTIONS}
)
set(LINK_OPTIONS "${PGO_OPTIONS};-flto=auto")

if (BUILD_CODE_COVERAGE)
	set(DEBUG_OPTIONS "${DEBUG_OPTIONS}" --coverage)
	set(RELEASE_OPTIONS "${RELEASE_OPTIONS}" --coverage)
endif ()

# target names
set(OBJECT_LIB_NAME "${PROJECT_NAME}o")
set(STATIC_LIB_NAME "${PROJECT_NAME}s")
set(SHARED_LIB_NAME "${PROJECT_NAME}so")
set(EXECUTABLE_NAME "${PROJECT_NAME}")
set(EXE_SHARED_NAME "${PROJECT_NAME}_shared")


include(exclude)
include(target-setup)
