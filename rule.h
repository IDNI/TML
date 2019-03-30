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
#include "defs.h"
#include "query.h"
#include "lp.h"
#include <functional>

struct rule { // a P-DATALOG rule in bdd form
	const bool neg;
	std::unordered_map<int_t, size_t> varmap;
	builtins<leq_const> *bts = 0;
	std::vector<builtins<unary_builtin<std::function<int(int)>>>>
		unary_builtins;
	std::vector<query> q;
	std::vector<ints> arities;
	ints harity, vars_arity, rels;
	int_t hrel;
	std::vector<size_t*> dbs;
	bdd_and_eq ae;
	void get_varmap(const matrix& v);

	rule(matrix v, const std::vector<size_t*>& dbs, size_t bits,size_t dsz);
	size_t fwd(size_t bits);
};

size_t fact(term v, size_t bits, size_t dsz);
size_t arlen(const ints& ar);
