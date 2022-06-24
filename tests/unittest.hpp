// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.

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

#define EXPECT_TRUE(A)        CHECK((A) == true)
#define EXPECT_FALSE(A)       CHECK((A) == false)

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
