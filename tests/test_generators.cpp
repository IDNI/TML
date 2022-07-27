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
#include "../src/generators.h"

TEST_SUITE("monotone_perm") {
	TEST_CASE("small cases") {
		for (int i = 0; i != 5; ++i) {
			std::vector<size_t> p0 = monotone_perm(i);
			std::cout << "vector: [";
			for (size_t e: p0) {
				std::cout << e << ",";
			}
			std::cout << "]" << std::endl;
		}

		// EXPECT_TRUE(!me);
	}
}


TEST_SUITE("monotone_grey_code_generators") {
	TEST_CASE("empty") {
		auto me = monotone_gray_code_generator(0);
		EXPECT_TRUE(!me);
	}
/*	TEST_CASE("non empty") {

		auto m = monotone_gray_code_generator(5);

		while (m) {
			auto vv = m();
			for (auto const v: vv) {
				std::cout << "vector: [";
				for (auto e: v) {
					std::cout << e << ",";
				}
				std::cout << "]" << std::endl;
			}
		}
	}*/
}
