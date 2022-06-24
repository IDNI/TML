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
#include "unittest.hpp"
#include "../src/iterators.h"

TEST_SUITE("grey_code_const_iterator") {
	TEST_CASE("grey_code_const_iterator empty iterator") {
		grey_code_const_iterator it;
		EXPECT_TRUE(it == grey_code_const_iterator::end);
	}
	TEST_CASE("grey_code_const_iterator non empty iterator") {

		#define TEST_GREY_CODE(v0, v1, v2, v3) \
			EXPECT_TRUE(v[0] == v0 && v[1] == v1 && v[2] == v2 && v[3] == v3); \
			++it; if (it != grey_code_const_iterator::end) v[*it] = 1 - v[*it];

		// extracted from Knuth Vol 4A
		grey_code_const_iterator it(4);
		std::vector<size_t> v(4);

		// the generated values are correct
		TEST_GREY_CODE(0,0,0,0);
		TEST_GREY_CODE(1,0,0,0);
		TEST_GREY_CODE(1,1,0,0);
		TEST_GREY_CODE(0,1,0,0);
		TEST_GREY_CODE(0,1,1,0);
		TEST_GREY_CODE(1,1,1,0);
		TEST_GREY_CODE(1,0,1,0);
		TEST_GREY_CODE(0,0,1,0);
		TEST_GREY_CODE(0,0,1,1);
		TEST_GREY_CODE(1,0,1,1);
		TEST_GREY_CODE(1,1,1,1);
		TEST_GREY_CODE(0,1,1,1);
		TEST_GREY_CODE(0,1,0,1);
		TEST_GREY_CODE(1,1,0,1);
		TEST_GREY_CODE(1,0,0,1);
		TEST_GREY_CODE(0,0,0,1);

		// we exhaust the iterator
		EXPECT_TRUE(it == grey_code_const_iterator::end);
	}
	TEST_CASE("power_set_const_iterator empty iterator") {
		std::vector<size_t> empty;
		power_set_const_iterator<size_t> it(empty);
		EXPECT_TRUE(it == power_set_const_iterator<size_t>::end);
	}
	TEST_CASE("power_set_const_iterator non empty iterator") {

		std::vector<size_t> v {1, 2, 3, 4};
		power_set_const_iterator it(v);

		// the generated values are correct
		std::vector<size_t> v0 = {}; EXPECT_TRUE(*it == v0); ++it;
		std::vector<size_t> v1 = {1}; EXPECT_TRUE(*it == v1); ++it;
		std::vector<size_t> v2 = {1, 2};  EXPECT_TRUE(*it == v2); ++it;
		std::vector<size_t> v3 = {2};  EXPECT_TRUE(*it == v3); ++it;
		std::vector<size_t> v4 = {2, 3};  EXPECT_TRUE(*it == v4); ++it;
		std::vector<size_t> v5 = {1, 2, 3};  EXPECT_TRUE(*it == v5); ++it;
		std::vector<size_t> v6 = {1, 3};  EXPECT_TRUE(*it == v6); ++it;
		std::vector<size_t> v7 = {3};  EXPECT_TRUE(*it == v7); ++it;
		std::vector<size_t> v8 = {3, 4};  EXPECT_TRUE(*it == v8); ++it;
		std::vector<size_t> v9 = {1, 3, 4};  EXPECT_TRUE(*it == v9); ++it;
		std::vector<size_t> v10 = {1, 2, 3, 4};  EXPECT_TRUE(*it == v10); ++it;
		std::vector<size_t> v11 = {2, 3, 4};  EXPECT_TRUE(*it == v11); ++it;
		std::vector<size_t> v12 = {2, 4};  EXPECT_TRUE(*it == v12); ++it;
		std::vector<size_t> v13 = {1, 2, 4};  EXPECT_TRUE(*it == v13); ++it;
		std::vector<size_t> v14 = {1, 4};  EXPECT_TRUE(*it == v14); ++it;
		std::vector<size_t> v15 = {4};  EXPECT_TRUE(*it == v15); ++it;

		// we exhaust the iterator
		EXPECT_TRUE(it == power_set_const_iterator<size_t>::end);
	}
}
