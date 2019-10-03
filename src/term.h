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
	bool neg = false, goal = false, iseq = false, isleq = false;
	ntable tab = -1;
	term() {}
	term(bool neg, bool eq, bool isleq, ntable tab, const ints& args) :
		ints(args), neg(neg), iseq(eq), isleq(isleq), tab(tab) {}
	bool operator<(const term& t) const {
		if (neg != t.neg) return neg;
		if (iseq != t.iseq) return iseq; // why not compare?
		if (isleq != t.isleq) return isleq;
		if (tab != t.tab) return tab < t.tab;
		if (goal != t.goal) return goal;
		return (const ints&)*this < t;
	}
	void replace(const std::map<int_t, int_t>& m);
};

std::wostream& operator<<(std::wostream& os, const term& t);
std::vector<term> to_vec(const term& h, const std::set<term>& b);
template<typename T> std::set<T> vec2set(const std::vector<T>& v, size_t n = 0);
