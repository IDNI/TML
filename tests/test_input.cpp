
#include "unittest.hpp"
#include <iostream>
#include <string>
#include <vector>
#include "../src/input.h"

TEST_SUITE("input processing test") {
    TEST_CASE("tokenizing input string") {
        cws emptyString = L"                                   ";
        lexemes emptyArray = prog_lex(emptyString);
        CHECK(emptyArray.size() == 0);
        cws stringWithComment = L" /*  ";
        DOCTEST_CHECK_THROWS(prog_lex(stringWithComment));
        cws s = L"setB(?x ?y ?z) :- e(?x), e(?y), ?x + ?y = ?z. ?x > ?y.";
        lexemes r = prog_lex(s);
        CHECK(r.size() == 27);
    }
}

