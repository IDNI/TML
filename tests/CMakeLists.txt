set(DOCTEST_CONFIG_ASSERTION_PARAMETERS_BY_VALUE "true")

add_executable(test_input test_input.cpp)
target_setup(test_input)
target_pass_features_on(test_input)
target_link_libraries(test_input ${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object ${TEST_FRAMEWORK})

add_executable(test_output test_output.cpp)
target_setup(test_output)
target_pass_features_on(test_output)
target_link_libraries(test_output ${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object ${TEST_FRAMEWORK})

add_custom_target(tmltest
	COMMAND test_input && tml_output && tml_earley
	DEPENDS test_input test_output test_earley)
