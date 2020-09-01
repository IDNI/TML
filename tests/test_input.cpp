
#include "unittest.hpp"
#include <iostream>
#include <string>
#include <vector>
#include "../src/input.h"

TEST_SUITE("input processing test") {
    TEST_CASE("tokenizing input string") {
        string_t emptyString = to_string_t("                                   ");
        input in1(emptyString.c_str());
        CHECK(in1.l.size() == 0);
        string_t stringWithComment = to_string_t(" /*  ");
	input in2(stringWithComment.c_str());
	DOCTEST_CHECK_THROWS(in2.prog_lex());
        string_t s = to_string_t(
		"setB(?x ?y ?z) :- e(?x), e(?y), ?x + ?y = ?z. ?x > ?y.");
	input in3(s.c_str());
	in3.prog_lex();
        CHECK(in3.l.size() == 27);
    }
}

