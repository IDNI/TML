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
public:
	bool neg = false, goal = false;
	enum textype { REL, EQ, LEQ, BLTIN, ARITH } extype = term::REL;
	t_arith_op arith_op = NOP;
	ntable tab = -1;
	size_t orderid = 0, nvars = 0;
	int_t idbltin = -1;
	argtypes types;
	//term() {} // to avoid wrong types, multivars initialization, use below
	term(bool neg_, textype extype_, t_arith_op arith_op, ntable tab_,
		 const ints& args, std::vector<ints> compvals_, const argtypes& types_,
		 size_t orderid_ = 0, size_t nvars_ = 0, bool hascompounds_ = false)
		: ints(args), neg(neg_), extype(extype_), arith_op(arith_op), tab(tab_),
		  orderid(orderid_), nvars(nvars_), types(types_),
		  hasmultivals(hascompounds_), compoundvals(compvals_) {
		DBG(check_hasmultivals(););
		hasmultivals = calc_hasmultivals(types);
		sync_multivals();
	}
	// this is the builtin .ctor overload
	term(bool neg_, ntable tab_, const ints& args, std::vector<ints> compvals_,
		 const argtypes& types_, size_t orderid_ = 0, int_t idbltin = -1, 
		 size_t nvars_ = 0, bool hascompounds_ = false)
		: ints(args), neg(neg_), extype(term::BLTIN), tab(tab_), 
		  orderid(orderid_), nvars(nvars_), idbltin(idbltin), types(types_),
		  hasmultivals(hascompounds_), compoundvals(compvals_) {
		DBG(check_hasmultivals(););
		hasmultivals = calc_hasmultivals(types);
		sync_multivals();
	}
	// simplified .ctor 
	term(ntable tab_, const ints& vals, const argtypes& types_,
		 bool hascompounds_ = false) // std::vector<ints> compvals_, 
		: ints(vals), neg(false), extype(term::REL), arith_op(NOP), tab(tab_),
		  orderid(0), nvars(0), types(types_), hasmultivals(hascompounds_), 
		  compoundvals(vals.size()) {
		DBG(check_hasmultivals(););
		hasmultivals = calc_hasmultivals(types);
		sync_multivals();
	}
	bool operator<(const term& t) const {
		if (neg != t.neg) return neg;
		//if (extype != t.extype) return extype < t.extype;
		if (tab != t.tab) return tab < t.tab;
		if (goal != t.goal) return goal;
		// D: TODO: order types, bltin...
		if (hasmultivals)
			return compoundvals < t.compoundvals;
		return (const ints&)*this < t;
	}
	void replace(const std::map<int_t, int_t>& m);

	const std::vector<ints>& multivals() const { 
		DBG(check_multivals(););
		return compoundvals; 
	}
	const ints& multivals(size_t arg) const { 
		DBG(check_multivals(arg););
		return compoundvals[arg];
	}
	bool is_multi(size_t arg) const { return compoundvals[arg].size() > 1; }
	bool is_const(size_t arg) const { 
		if (!is_multi(arg))
			return (*this)[arg] >= 0;
		for (int_t val : compoundvals[arg]) if (val < 0) return false;
		return true;
	}
	void set_multivals(size_t arg, ints vals) {
		compoundvals[arg] = std::move(vals);
		hasmultivals = true;
	}

	inline static bool calc_hasmultivals(const argtypes& types) {
		for (auto type : types) if (type.isCompound()) return true;
		return false;
	}

private:
	void sync_multivals() {
		for (size_t arg = 0; arg < size(); ++arg) {
			ints& vals = compoundvals[arg];
			if (vals.empty() || (*this)[arg] != vals[0]) {
				if (is_multi(arg))
					throw std::runtime_error("term: multivals not in sync??");
				vals = ints{ (*this)[arg] };
			}
		}
	}

#ifdef DEBUG
	void check_multivals(size_t arg) const {
		if (compoundvals[arg].empty() ||
			compoundvals[arg][0] != (*this)[arg])
			throw std::runtime_error("check_multivals: multivals?");
	}

	void check_multivals() const {
		for (size_t arg = 0; arg < size(); ++arg)
			if (compoundvals[arg].empty() ||
				compoundvals[arg][0] != (*this)[arg]) {
				if (types[arg].isCompound())
					throw std::runtime_error("check_multivals: multivals?");
				//o::dump() << L"check_multivals: multivals?" << std::endl;
			}
	}

	void check_hasmultivals() const {
		//if (calc_hasmultivals(types) != hasmultivals)
		//	o::dump() << L"check_multivals: multivals?" << endl;
		//	//throw std::runtime_error("check_multivals: multivals?");
	}
#endif

	bool hasmultivals = false; // for fast check during op<, something smarter?
	std::vector<ints> compoundvals;
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