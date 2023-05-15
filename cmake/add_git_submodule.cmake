cmake_minimum_required(VERSION 3.6)

function(add_git_submodule dir)
	find_package(Git REQUIRED)
	if(NOT EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/${dir}/CMakeLists.txt)
		execute_process(COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive -- ${dir}
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
			COMMAND_ERROR_IS_FATAL ANY)
	endif()
	add_subdirectory(${dir})
endfunction(add_git_submodule)