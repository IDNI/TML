# setups a target: sets COMPILE and LINK options, adds warnings, c++20 req...
function(target_setup target)
	target_compile_features(${target} PRIVATE cxx_std_20)
	if(NOT MSVC)
		target_compile_options(${target} PRIVATE
			-W -Wall -Wextra -Wpedantic
			-Wformat=2
			-Wno-variadic-macros
			-Wcast-align
			-Wstrict-aliasing=2
			-Wstrict-overflow=5
			-Wfloat-equal
			-Wwrite-strings
			-Wno-missing-braces
			-Wno-parentheses-equality
			-Wno-unqualified-std-cast-call
			-Wno-unused-value
		)
	else()
		target_compile_options(${target} PRIVATE /W4)
	endif()
	target_compile_options(${target} PRIVATE "${COMPILE_OPTIONS}")
	target_link_libraries(${target} ${CMAKE_THREAD_LIBS_INIT})
	target_link_options(${target} PRIVATE "${LINK_OPTIONS}")	
	target_include_directories(${target}
		PRIVATE
			${CMAKE_CURRENT_SOURCE_DIR}/src
		PUBLIC
			$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/src>
			$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
	)
	set_target_properties(${target} PROPERTIES
		ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
		LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
		RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
		PUBLIC_HEADER            "${PROJECT_HEADERS}"
	)
endfunction()
