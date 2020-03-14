//
// Created by ak on 06.03.2020.
//

#ifndef TML_UNITTEST_HPP
#define TML_UNITTEST_HPP

#ifdef NDEBUG
#undef NDEBUG
#endif
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include <string>
#include <iostream>
#include "../src/doctest.h"

namespace testing = doctest;

#define TEST(A, B)            TEST_CASE(#A "." #B)

#define EXPECT_TRUE(A)        CHECK(A)
#define EXPECT_FALSE(A)       CHECK_FALSE(A)

#define EXPECT_EQ(A, B)       CHECK_EQ(A, B)
#define EXPECT_NE(A, B)       CHECK_NE(A, B)
#define EXPECT_LT(A, B)       CHECK_LT(A, B)
#define EXPECT_LE(A, B)       CHECK_LE(A, B)
#define EXPECT_GT(A, B)       CHECK_GT(A, B)
#define EXPECT_GE(A, B)       CHECK_GE(A, B)
#define EXPECT_NEAR(A, B, C)  CHECK(A == doctest::Approx(B).epsilon(C))

#define EXPECT_THROW(A, B)    CHECK_THROWS_AS(A, B)

#define TYPED_TEST_SETUP(ID, TYPES)             \
    using ID = TYPES

#define TYPED_TEST(ID, NAME)                    \
    TEST_CASE_TEMPLATE(#ID "." #NAME, TypeParam, ID)

#endif //TML_UNITTEST_HPP
