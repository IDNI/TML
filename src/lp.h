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
#include "query.h"
#include "term.h"

void tml_init();

typedef std::map<prefix, size_t*> db_t;
typedef std::map<prefix, size_t> diff_t;

struct prog_data {
	strs_t strs;
	std::unordered_map<int_t, term> strtrees;
	std::vector<term> out;
	matpairs r;
	matrix goals, tgoals;
};

class lp { // [pfp] logic program
	friend struct rule;
	DBG(friend class driver;)
	std::vector<struct rule*> rules;
	void add_fact(size_t f, const prefix& p);
	bool add_not_fact(size_t f, const prefix& p);
	bool add_facts(const matrix& x);
	bool add_fact(const term& t);
	void get_trees();
	void fwd(diff_t &add, diff_t &del);
	const strs_t strs;
	diff_t trees, gbdd;
public:
	prog_data pd;
	range rng;
	db_t db;
	diff_t trees_out;
	lp(prog_data, range rng, lp *prev = 0);
	bool pfp(std::function<matrix(diff_t)> mkstr);
	~lp();
};

extern int_t null;
#endif
