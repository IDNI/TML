    set(DOCTEST_CONFIG_ASSERTION_PARAMETERS_BY_VALUE "true")

    set(TML_TESTS
            test_input.cpp
            )

    add_executable(test_tml ${TML_TESTS})

    target_compile_features(test_tml PRIVATE cxx_std_17)
    target_compile_options(test_tml PRIVATE "-Wall" "-Wno-deprecated")
    target_link_libraries(test_tml TMLo ${TEST_FRAMEWORK})

    add_custom_target(tmltest COMMAND test_tml DEPENDS test_tml)
