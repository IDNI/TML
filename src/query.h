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
	spbdd z;
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
	DBG(term _t;)
	bdd_and_eq ae;
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
		if (it == memo.end()) {
			spbdd r = compute(x, 0);
			DBG(assert_nvars(r, bits*args);)
			return onmemo(), memo[x] = r;
		}
		DBG(assert_nvars(it->second, bits*args);)
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

struct range {
	const int_t syms, nums, chars;
	const size_t bits;
	struct key {
		size_t arg, args;
		int_t ext;
		bool operator<(const key& k) const {
			if (arg != k.arg) return arg < k.arg;
			if (args != k.args) return args < k.args;
			if (ext != k.ext) return ext < k.ext;
			return false;
		}
	};
	static std::map<key, builtins<leq_const>>
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
#endif
