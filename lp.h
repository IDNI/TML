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

//template<> struct std::hash<std::pair<size_t, bools>> {
//	size_t operator()(const std::pair<size_t, bools>& m) const; };
//template<> struct std::hash<std::pair<int_t, ints>> {
//	size_t operator()(const std::pair<int_t, ints>&) const; };

class lp { // [pfp] logic program
	friend struct rule;
	std::vector<struct rule*> rules;
	matrix pgoals;
//	void term_pad(term& t);
//	void rule_pad(matrix& t);
//	matrix rule_pad(const matrix& t);
//	void rules_pad(matrices& t);
//	matrices get_proof1() const;
//	matrices get_proof2() const;
	bool add_fact(const term& t);
	size_t prove() const;
	lp *prev, *proof1 = 0, *proof2 = 0;
	size_t gbdd = F;
public:
	size_t bits, dsz;
	typedef std::map<std::pair<int_t, ints>, size_t*> db_t;
	typedef std::map<std::pair<int_t, ints>, size_t> diff_t;
	db_t db, ndb;

	lp(matrices r, matrix g, matrix pg, size_t dsz, lp *prev = 0);
	void fwd(diff_t &add, diff_t &del);
	bool pfp();

	size_t get_sym_bdd(size_t sym, size_t pos) const;
	size_t get_varbdd(size_t ar) const;
//	size_t maxw() const;
	~lp();
};

std::wostream& out(std::wostream& os, const node& n); // print bdd in ?: syntax
std::wostream& out(std::wostream& os, size_t n);
extern int_t null;
#endif
