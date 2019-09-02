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

struct term : public ints {
	bool neg, goal = false;
	bool iseq;
	ntable tab;
	term() {}
	term(bool neg, bool eq, ntable tab, const ints& args) :
		ints(args), neg(neg), iseq(eq), tab(tab) {}
	bool operator<(const term& t) const {
		if (neg != t.neg) return neg;
		if (iseq != t.iseq) return iseq < t.iseq;
		if (tab != t.tab) return tab < t.tab;
		if (goal != t.goal) return goal;
		return (const ints&)*this < t;
	}
	void replace(const std::map<int_t, int_t>& m);
};

