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
#include <iostream>
#include "bdd.h"

const int_t pad = 0;

void tml_init();

#define msb(x) ((sizeof(unsigned long long)<<3) - \
	__builtin_clzll((unsigned long long)(x)))

class lp { // [pfp] logic program
	std::vector<class rule*> rules;
	void step(); // single pfp step
	const size_t bits, ar, dsz;
	size_t db = F; // db's bdd root
public:
	lp(size_t maxbits, size_t arity, size_t dsz) :
		bits(maxbits), ar(arity), dsz(dsz) {}
	void rule_add(const matrix& t);
	void compile(size_t nsyms);
	bool pfp();
	matrix getdb();
};
