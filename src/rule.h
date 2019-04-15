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
#include "lp.h"
#include <functional>

struct rule { // a P-DATALOG rule in bdd form
	typedef std::unordered_map<int_t, size_t> varmap;
	bools neg;
	std::vector<varmap> hvars;
	spbdd bleq;
	bdds hleq;
	std::vector<query> q;
	std::vector<prefix> hpref;
	std::vector<std::pair<bools, sizes>> dt;
	size_t maxhlen, nvars;
	std::vector<db_t::iterator> dbs;
	std::vector<sizes> hperm;
	std::vector<bdd_and_eq> ae;
	range rng;
	sizes get_perm(const term& b, varmap&);
	void get_ranges(const matrix& h, const matrix& b, const varmap&);

	rule(matrix h, matrix b, const std::vector<db_t::iterator>& dbs,
		range& rng);
	bdds fwd();
};

spbdd fact(const term& v, range&);
