find_program(CLANG_FORMAT NAMES clang-format-9 clang-format)
if (CLANG_FORMAT)
    message(STATUS "Found clang-format")
    configure_file("${PROJECT_SOURCE_DIR}/clang-format.sh.in"
            "${CMAKE_BINARY_DIR}/clang-format.sh" @ONLY)
    add_custom_target(clang-format COMMAND bash "${CMAKE_BINARY_DIR}/clang-format.sh")
else ()
    message(WARNING "Clang-format not found!")
endif ()
