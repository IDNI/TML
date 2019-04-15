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
#ifndef __QUERY_H__
#define __QUERY_H__
#include <algorithm>
#include <numeric>
#include <map>
#include "bdd.h"
#include "term.h"

class bdd_and_eq {
	DBG(term _t;)
	struct key {
		const size_t bits, nvars;
		const ints e;
		const bool neg;
		bool operator<(const key& k) const {
			if (nvars != k.nvars) return nvars < k.nvars;
			if (e.size() != k.e.size()) return e.size()<k.e.size();
			if (neg != k.neg) return neg;
			return e != k.e ? e < k.e : false;
		}
		key(size_t bits, size_t nvars, const ints& e, bool neg) :
			bits(bits), nvars(nvars), e(e), neg(neg) {}
	} k;
	static std::map<key, std::unordered_map<spbdd, spbdd>> memos;
	std::unordered_map<spbdd, spbdd>& m;
public:
	bdd_and_eq(size_t bits, const term& t, bool neg);
	spbdd operator()(spbdd x, spbdd y);
	static void memo_clear() {
		for (auto x : memos) {
			onmemo(-x.second.size()); 
			x.second.clear();
			//delete x.second;
		}
//		memos.clear();
	}
};

class query {
	const bools ex;
	const bool neg;
	const sizes perm;
/*	struct key {
		bool operator<(const key& k) const {
			if (neg != k.neg) return neg;
			if (ex.size()!=k.ex.size())return ex.size()<k.ex.size();
			if (ex != k.ex) return ex < k.ex;
			return perm != k.perm ? perm < k.perm : false;
		}
		key(const bools& ex, bool neg, const sizes& perm) :
			ex(ex), neg(neg), perm(perm) {}
	} k;*/
	bdd_and_eq ae;
//	sizes getdom() const;
//	static std::map<key, std::unordered_map<size_t, size_t>*> memos;
//	std::unordered_map<size_t, size_t>* m;
//	size_t compute(size_t x, size_t v);
public:
	query(size_t bits, const term& t, const sizes& perm, bool neg);
	spbdd operator()(spbdd x);
};

enum builtin_res { PASS, FAIL, CONTHI, CONTLO, CONTBOTH };
template<typename T> T sort(const T& x);

template<typename func> class builtins {
	const size_t arg, bits, args, nvars;
	bools path;
	sizes getdom() const;
	int_t get_int(size_t pos) const;
	std::unordered_map<spbdd, spbdd> memo;
	func f;

	spbdd compute(spbdd x, size_t v) {
		if (x->leaf() && !x->trueleaf()) return F;
		if (ARG(v, args) != arg) return compute(x, v+1);
		spbdd h, l;
		path[v] = true;
		switch (f(path, arg, v)) {
			case FAIL: h = F; break;
			case PASS: h = T; break;
			case CONTBOTH: h = compute(x->h(), v+1); break;
			default: throw 0;
		}
		path[v] = false;
		switch (f(path, arg, v)) {
			case FAIL: l = F; break;
			case PASS: l = T; break;
			case CONTBOTH: l = compute(x->l(), v+1); break;
			default: throw 0;
		}
		return bdd::add(v+1, h, l);
	}
public:
	builtins(size_t arg, size_t bits, size_t args, func f) 
		: arg(arg), bits(bits), args(args), nvars(bits*args)
		, path(nvars,0), f(f) {}

	spbdd operator()(spbdd x) {
		auto it = memo.find(x);
		if (it == memo.end()) return onmemo(), memo[x] = compute(x, 0);
		return it->second;
	}
	void memo_clear() { onmemo(-memo.size()); memo.clear(); }
};

struct leq_const {
	const int_t c;
	const size_t bits, args;
	leq_const(int_t c, size_t bits, size_t args) : c(c), bits(bits)
		, args(args) { } //assert(c>>2 < (1<<bits)); }
	builtin_res operator()(const bools& path, size_t arg, size_t v) const{
		return	path[v] ? (c&(1<<(BIT(v,args,bits)))) ? 
			v == POS(0, bits, arg, args) ? PASS : CONTBOTH : FAIL :
			(c&(1<<(BIT(v,args,bits)))) ||
			v == POS(0, bits, arg, args) ? PASS : CONTBOTH;
	}
};

/*struct geq_const {
	const int_t c;
	const size_t bits, args;
	geq_const(int_t c, size_t bits, size_t args) : c(c), bits(bits)
		, args(args) { assert(c < (1<<bits)); }
	builtin_res operator()(const std::vector<char>& path, size_t arg,
		size_t var) const;
};*/

DBG(using namespace std;)

struct range {
	const int_t syms, nums, chars;
	const size_t bits;
	static std::map<std::pair<size_t, int_t>, builtins<leq_const>>
		bsyms, bnums, bchars;
	static std::unordered_map<std::array<int_t, 5>, spbdd,
		array_hash<int_t, 5>> memo;

	range(int_t syms, int_t nums, int_t chars)
	: syms(syms), nums(nums), chars(chars), bits(msb(syms+nums+chars)+2) {}

	spbdd operator()(const sizes& domain, size_t nargs) {
		bdds v;
		for (size_t x : domain) v.push_back((*this)(x, nargs));
		return bdd_and_many(move(v));
	}
	spbdd operator()(size_t arg, size_t nargs);
	static void memo_clear() {
		onmemo(-memo.size()), memo.clear();
		for (auto x : bsyms) x.second.memo_clear();
		for (auto x : bnums) x.second.memo_clear();
		for (auto x : bchars) x.second.memo_clear();
	}
};

/*
template<typename func> struct unary_builtin {
	const std::set<int_t> vals;
	const bool neg;
	const size_t bits, args;
	const leq_const lt;
	const geq_const gt;

	std::set<int_t> get_vals(func f, size_t from, size_t to) const {
		std::set<int_t> r;
		for (; from != to; ++from) if (f(from)) r.insert(from);
		return r;
	}

	unary_builtin(bool neg, func f, size_t from, size_t to, size_t bits,
		size_t args) : vals(get_vals(f, from, to)), neg(neg), bits(bits)
		, args(args), lt(*vals.rbegin(), bits, args)
		, gt(*vals.begin(), bits, args) {}

	builtin_res operator()(const bools& path, size_t arg,
		size_t var) const {
		if (ARG(var, args) != arg) return CONTBOTH;
		builtin_res l = lt(path, arg, var);
		if (l == FAIL) return neg ? PASS : FAIL;
		builtin_res g = gt(path, arg, var);
		if (g == FAIL || (l == CONTLO && g == CONTHI))
			return neg ? PASS : FAIL;
		if (l == CONTLO) return CONTLO;
		if (g == CONTHI) return CONTHI;
		if (var != args*bits) return CONTBOTH;
		int_t v = 0;
		size_t n = POS(0, bits, arg, args);
		for (; n < POS(0, bits, arg+1, args); n += args)
			if (path[n] == 1)
				v |= (1 << (bits-n%bits-1));
			DBG(else assert(path[n]);)
		return	neg ? vals.find(v) != vals.end() ? PASS : FAIL :
			vals.find(v) == vals.end() ? PASS : FAIL;
	}
};*/
#endif
