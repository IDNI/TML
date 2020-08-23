find_program (BASH_EXECUTABLE bash)
find_program (WC_EXECUTABLE wc)

if (BASH_EXECUTABLE AND WC_EXECUTABLE)
    configure_file("${PROJECT_SOURCE_DIR}/tml-check.sh.in"
            "${CMAKE_BINARY_DIR}/tml-check.sh" @ONLY)
    add_custom_target(tml-check COMMAND bash "${CMAKE_BINARY_DIR}/tml-check.sh")
else ()
    message(WARNING "bash or wc executables not found!")
endif ()
