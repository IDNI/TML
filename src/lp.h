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

void tml_init();

typedef std::map<std::pair<int_t, ints>, size_t*> db_t;
typedef std::map<std::pair<int_t, ints>, size_t> diff_t;

class lp { // [pfp] logic program
	friend struct rule;
	DBG(friend class driver;)
	std::vector<struct rule*> rules;
	void add_fact(size_t f, int_t rel, ints arity);
	bool add_not_fact(size_t f, int_t rel, ints arity);
	bool add_facts(const matrix& x);
	bool add_fact(const term& t);
	void get_trees();
	void fwd(diff_t &add, diff_t &del);
	const strs_t strs;
	diff_t trees, trees_out;
public:
	db_t db;
	range rng;
	lp(matpairs r, matrix g, const strs_t&, range rng, lp *prev = 0);
	bool pfp(std::function<matrix(diff_t)> mkstr);
	~lp();
};

size_t arlen(const ints& ar);
std::set<ints> prefix(const db_t& db, ints ar, int_t rel);
void get_tree(int_t rel, size_t root, ints ar, const db_t& db, size_t bits,
	diff_t& res);
extern int_t null;
#endif
