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
#include <map>
#include "defs.h"
#include "lp.h"

struct rule { // a P-DATALOG rule in bdd form
	struct body {
		size_t sel = T;
		const bool neg;
		bools ex;
		std::vector<size_t> perm, eqs;
		body(term &t, size_t ar, size_t bits, size_t dsz, size_t nvars);
		void from_arg(int_t vij, size_t j, size_t bits, size_t dsz,
			std::map<int_t, size_t>& m);
		size_t varbdd(size_t db, lp::step& p) const;
	};
	bool neg = false;
	size_t hsym = T, vars_arity; //proof_arity = 0
	std::vector<body> bd;
	std::vector<size_t> eqs;
	std::set<size_t> p;
	matrix proof1;
	matrices proof2, proof3;

	rule() {}
	rule(matrix v, size_t bits, size_t dsz, bool proof);
	size_t fwd(size_t db, size_t bits, size_t ar, lp::step& s);
	size_t get_varbdd(size_t bits, size_t ar) const;
};
