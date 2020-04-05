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
#ifndef __TERM_H__
#define __TERM_H__
#include "defs.h"
#include "types.h"

struct term : public ints {
	bool neg = false, goal = false;
	enum textype { REL, EQ, LEQ, BLTIN, ARITH } extype = term::REL;
	t_arith_op arith_op = NOP;
	ntable tab = -1;
	size_t orderid = 0, nvars = 0;
	// D: TODO: builtins are very different, handle as a same size union struct?
	int_t idbltin = -1; // size_t bltinsize;
	argtypes types;
	ints nums;
	term() {}
	term(bool neg_, textype extype_, t_arith_op arith_op, ntable tab_,
		 const ints& args, const argtypes& types_, const ints& nums_,
		 size_t orderid_, size_t nvars_)
		: ints(args), neg(neg_), extype(extype_), arith_op(arith_op), tab(tab_),
		  orderid(orderid_), nvars(nvars_), types(types_), nums(nums_) {}
	term(bool neg_, ntable tab_, const ints& args, const argtypes& types_,
		 const ints& nums_, size_t orderid_, int_t idbltin, size_t nvars_)
		: ints(args), neg(neg_), extype(term::BLTIN), tab(tab_), 
		  orderid(orderid_), nvars(nvars_), idbltin(idbltin), types(types_), 
		  nums(nums_) {}
	bool operator<(const term& t) const {
		if (neg != t.neg) return neg;
		//if (extype != t.extype) return extype < t.extype;
		if (tab != t.tab) return tab < t.tab;
		if (goal != t.goal) return goal;
		// D: TODO: order types, bltin...
		return (const ints&)*this < t;
	}
	void replace(const std::map<int_t, int_t>& m);
};

std::wostream& operator<<(std::wostream& os, const term& t);
std::vector<term> to_vec(const term& h, const std::set<term>& b);
template<typename T> std::set<T> vec2set(const std::vector<T>& v, size_t n = 0);

typedef std::set<std::vector<term>> flat_prog;

struct natcmp {
	bool operator()(const term& l, const term& r) const {
		if (l.orderid != r.orderid) return l.orderid < r.orderid;
		if (l.neg != r.neg) return l.neg;
		//if (iseq != t.iseq) return iseq;
		//if (isleq != t.isleq) return isleq;
		//if (extype != t.extype) return extype < t.extype;
		//if (l.tab != r.tab) return l.tab < r.tab;
		if (l.goal != r.goal) return l.goal;
		return (const ints&)l < r;
	}
};
typedef std::set<term, natcmp> term_set;

#endif // __TERM_H__