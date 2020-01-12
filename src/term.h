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
	bool neg = false, goal = false;
	enum textype { REL, EQ, LEQ, BLTIN, ALU } extype = term::REL;
	t_alu_op alu_op = NOP;
	ntable tab = -1;
	size_t orderid = 0;
	// D: TODO: builtins are very different, handle as a same size union struct?
	int_t idbltin = -1; // size_t bltinsize;
	term() {}
	term(bool neg, textype extype, t_alu_op alu_op, ntable tab, const ints& args, size_t orderid)
		: ints(args), neg(neg),extype(extype), alu_op(alu_op), tab(tab), orderid(orderid) {}
	// builtins .ctor
	term(bool neg, ntable tab, const ints& args, size_t orderid, int_t idbltin)
		: ints(args), neg(neg), extype(term::BLTIN), tab(tab), orderid(orderid),
		idbltin(idbltin) {}
	bool operator<(const term& t) const {
		if (neg != t.neg) return neg;
		//if (extype != t.extype) return extype < t.extype;
		//if (isalu != t.isalu) return isalu;
		if (tab != t.tab) return tab < t.tab;
		if (goal != t.goal) return goal;
		return (const ints&)*this < t;
	}
	void replace(const std::map<int_t, int_t>& m);
};

std::wostream& operator<<(std::wostream& os, const term& t);
std::vector<term> to_vec(const term& h, const std::set<term>& b);
template<typename T> std::set<T> vec2set(const std::vector<T>& v, size_t n = 0);
