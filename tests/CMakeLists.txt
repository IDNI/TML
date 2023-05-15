set(DOCTEST_CONFIG_ASSERTION_PARAMETERS_BY_VALUE "true")

add_executable(test_output test_output.cpp)
target_setup(test_output)
target_pass_features_on(test_output)
target_link_libraries(test_output ${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object ${TEST_FRAMEWORK})

set(TEST_ITERATORS test_iterators.cpp)
add_executable(test_iterators ${TEST_ITERATORS})
target_setup(test_iterators)
target_link_libraries(test_iterators ${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object ${TEST_FRAMEWORK})

set(TEST_TRANSFORM_OPT test_transform_opt.cpp)
add_executable(test_transform_opt ${TEST_TRANSFORM_OPT})
target_setup(test_transform_opt)
target_link_libraries(test_transform_opt ${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object ${TEST_FRAMEWORK})

add_custom_target(tmltest
	COMMAND test_output && test_iterators && test_transform_opt
	DEPENDS test_output test_iterators test_transform_opt)

add_test(NAME test_iterators COMMAND "${PROJECT_BINARY_DIR}/test_iterators")
add_test(NAME test_output COMMAND "${PROJECT_BINARY_DIR}/test_output")
# add_test(NAME test_transform_opt COMMAND "${PROJECT_BINARY_DIR}/test_transform_opt")

find_program (BASH_PROGRAM bash)
if (BASH_PROGRAM)
	add_test (regression ${BASH_PROGRAM} ${CMAKE_CURRENT_SOURCE_DIR}/run_all_regression_tests.sh)
endif (BASH_PROGRAM)