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
#include <cstdint>
#include <vector>
#include <forward_list>
#include <iostream>
#include "bdd.h"

const int_t pad = 0;

void tml_init();

#define msb(x) ((sizeof(unsigned long long)<<3) - \
	__builtin_clzll((unsigned long long)(x)))

class lp { // [pfp] logic program
	std::forward_list<matrix> rawrules;
	std::vector<class rule*> rules;
	void step(); // single pfp step
public:
	size_t bits, ar = 0, maxw = 0;
	size_t db = F; // db's bdd root
	bool pfp();
	void printdb(std::wostream& os);
	void rule_add(const matrix& t);
	void compile(size_t bits, size_t nsyms);
	vbools allsat(size_t x);
};
