if(NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif()

# adds git definitions
include(git-defs)
function(target_git_definitions target)
	target_compile_definitions(${target} PRIVATE ${GIT_DEFINITIONS})
endfunction()

# sets all outputs to a build directory
function(target_build_output target)
	set_target_properties(${target} PROPERTIES
		ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
		LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
		RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
endfunction()

# setups a target: adds warnings, c++17, git defs and sets output directory
function(target_setup target)
	if(MSVC)
		target_compile_options(${target} PRIVATE /W4)
	else()
		target_compile_options(${target} PRIVATE
			-W -Wall -Wextra -Wpedantic)
	endif()
	target_compile_features(${target} PRIVATE cxx_std_17)
	target_git_definitions(${target})
	target_build_output(${target})
endfunction()
