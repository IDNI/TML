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
#include "bdd.h"
#include <algorithm>
#include <numeric>

class bdd_and_eq {
	const size_t bits, nvars;
	const ints e;
	const bool neg;
	DBG(term _t;)
	std::unordered_map<size_t, size_t> memo, negmemo;
public:
	bdd_and_eq(size_t bits, const term& t, bool neg);
	size_t operator()(const size_t x);
};

class query {
	const bools ex;
	const bool neg;
	sizes perm;
	bdd_and_eq ae;
//	sizes getdom() const;
	std::unordered_map<size_t, size_t> memo, negmemo;
//	size_t compute(size_t x, size_t v);
public:
	query(size_t bits, const term& t, const sizes& perm, bool neg);
	size_t operator()(size_t x);
};

enum builtin_res { PASS, FAIL, CONTHI, CONTLO, CONTBOTH };
template<typename T> T sort(const T& x);

template<typename func> class builtins {
	const size_t arg, bits, args, nvars;
	bools path;
	sizes getdom() const;
	int_t get_int(size_t pos) const;
	std::unordered_map<size_t, size_t> memo;
	func f;

	size_t compute(size_t x, size_t v) {
		if (leaf(x) && !trueleaf(x)) return F;
		if (ARG(v, args) != arg) return compute(x, v+1);
		size_t h, l;
		const node n = getnode(x);
		path[v] = true;
		switch (f(path, arg, v)) {
			case FAIL: h = F; break;
			case PASS: h = T; break;
			case CONTBOTH: h = compute(n[1], v+1); break;
			default: throw 0;
		}
		path[v] = false;
		switch (f(path, arg, v)) {
			case FAIL: l = F; break;
			case PASS: l = T; break;
			case CONTBOTH: l = compute(n[2], v+1); break;
			default: throw 0;
		}
		return bdd_add({{v+1, h, l}});
	}
public:
	builtins(size_t arg, size_t bits, size_t args, func f) 
		: arg(arg), bits(bits), args(args), nvars(bits*args)
		, path(nvars,0), f(f) {}

	size_t operator()(size_t x) {
		auto it = memo.find(x);
		if (it == memo.end()) return memo[x] = compute(x, 0);
		return it->second;
	}
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
	static std::unordered_map<std::array<int_t, 5>, size_t,
		array_hash<int_t, 5>> memo;

	range(int_t syms, int_t nums, int_t chars)
	: syms(syms), nums(nums), chars(chars), bits(msb(syms+nums+chars)+2) {}

	size_t operator()(const sizes& domain, size_t nargs) {
		sizes v;
		for (size_t x : domain) v.push_back((*this)(x, nargs));
		return bdd_and_many(v);
	}
	size_t get_leq(size_t arg, size_t nargs, int_t c) const {
		size_t r = builtins<leq_const>(arg, bits, nargs,
				leq_const(c, bits, nargs))(T);
	//	DBG(wcout<<"get_leq c="<<c<<" arg="<<arg<<" args="<<nargs
	//		<<endl<<allsat(r,bits,nargs)<<endl;)
	//	DBG(bdd_out(wcout, r)<<endl);
		return r;
	}
	size_t get2(size_t arg, size_t args, bool b1, bool b2) const {
		return bdd_and(	from_bit(POS(0,bits,arg,args), b1),
				from_bit(POS(1,bits,arg,args), b2));
	}
	size_t get_leq2(size_t arg, size_t nargs,int_t c,bool b1,bool b2) const{
		if (!c) return bdd_and_not(T, get2(arg,nargs, b1, b2));
		return bdd_and(	get2(arg, nargs, b1, b2),
				get_leq(arg, nargs, ((c-1)<<2)|3));
	}
	size_t operator()(size_t arg, size_t nargs) {
		auto it = memo.find({syms,nums,chars,(int_t)nargs,(int_t)arg});
		if (it != memo.end()) return it->second;
		size_t r;
		DBG(using namespace std;)
		r = bdd_and_many({
				get_leq2(arg, nargs, chars, true, false),
				get_leq2(arg, nargs, nums, false, true),
				get_leq2(arg, nargs, syms, false, false)});
	//	DBG(wcout<<"r:"<<endl<<allsat(r, bits,nargs)<<endl;)
	//	DBG(bdd_out(wcout<<endl, r)<<endl);
		return memo[{syms,nums,chars,(int_t)nargs,(int_t)arg}] = r;
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
