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
#ifndef __LP_H__
#define __LP_H__
#include <cstdint>
#include <vector>
#include <iostream>
#include <set>
#include <map>
#include "bdd.h"

void tml_init();

class lp { // [pfp] logic program
	friend struct rule;
	std::vector<struct rule*> rules;
	bool add_fact(size_t f, int_t rel, ints arity);
	bool add_not_fact(size_t f, int_t rel, ints arity);
	lp *prev;
	size_t gbdd = F;
public:
	typedef std::map<std::pair<int_t, ints>, size_t*> db_t;
	typedef std::map<std::pair<int_t, ints>, size_t> diff_t;
	void align(const db_t& d, const db_t& nd, size_t pbits, size_t bits);
	db_t db, ndb;
	const size_t bits, dsz;
	const int_t outrel;
	const strs_t strs;

	lp(matrices r, matrix g, int_t outrel, size_t dsz, const strs_t&,
		lp *prev = 0);
	void fwd(diff_t &add, diff_t &del);
	bool pfp();

	bool add_fact(const term& t);
	~lp();
};

std::wostream& out(std::wostream& os, const node& n); // print bdd in ?: syntax
std::wostream& out(std::wostream& os, size_t n);
extern int_t null;
#endif
