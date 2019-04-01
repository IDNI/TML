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
#include "bdd.h"
#include <algorithm>

class query {
	const size_t bits, nvars;
	const ints e;
	const sizes perm, domain;
	std::vector<char> path;
	const bool neg;
	sizes getdom() const;
	std::unordered_map<size_t, size_t> memo, negmemo;
	size_t compute(size_t x, size_t v);
public:
	query(size_t bits, const term& t, const sizes& perm, bool neg);
	size_t operator()(size_t x);
};

class bdd_and_eq {
	const size_t bits, nvars;
	const ints e;
	DBG(term _t;)
	std::unordered_map<size_t, size_t> memo;
public:
	bdd_and_eq(size_t bits, const term& t);
	size_t operator()(size_t x);
};

enum builtin_res { PASS, FAIL, CONTHI, CONTLO, CONTBOTH };
template<typename T> T sort(const T& x);
#define has(x, y) std::binary_search(x.begin(), x.end(), y)
#define del(x, y) x.erase(std::equal_range(x.begin(), x.end(), y).first)

template<typename func> class builtins {
	const size_t bits, args, nvars;
	sizes domain;
	std::vector<char> path;
	sizes getdom() const;
	int_t get_int(size_t pos) const;
	std::unordered_map<size_t, size_t> memo;
	func f;

	size_t compute(size_t x, size_t v) {
		if (leaf(x) && (!trueleaf(x) || v == nvars)) return x;
		node n = getnode(x);
		assert(v<nvars);
		if (!has(domain, ARG(v, args)/*v/bits*/))
			return	++v, bdd_add({{v, compute(n[1], v),
				compute(n[2], v)}});
		if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
		switch (f(path, ARG(v, args)/*(v/bits)*/*bits, v+1)) {
			case FAIL: return F;
			case CONTHI:path[v] = 1;
				   return bdd_add({{v+1,compute(n[1],v+1),F}});
			case CONTLO:path[v] = -1;
				    return bdd_add({{v+1,F,compute(n[2],v+1)}});
			case PASS: return T; //del(domain, v/bits);
			default: ;
		}
		return	path[v] = 1, x = compute(n[1], v+1), path[v++] = -1,
			bdd_add({{v, x, compute(n[2], v)}});
	}
public:
	builtins(size_t bits, size_t args, func f) : bits(bits)
		, args(args), nvars(bits*args) , domain(sort(f.domain)),
		path(nvars,0), f(f) {}

	size_t operator()(size_t x) {
		auto it = memo.find(x);
		if (it == memo.end()) return memo[x] = compute(x, 0);
		return it->second;
	}
};

struct leq_const {
	const int_t c;
	const size_t bits;
	const sizes domain;
	leq_const(const sizes& domain, int_t c, size_t bits) : c(c), bits(bits)
		, domain(domain) { assert(c < (1<<bits)); }
	builtin_res operator()(const std::vector<char>& path, size_t from,
		size_t to) const;
};

struct geq_const {
	const int_t c;
	const size_t bits;
	const sizes domain;
	geq_const(const sizes& domain, int_t c, size_t bits) : c(c), bits(bits)
		, domain(domain) { assert(c < (1<<bits)); }
	builtin_res operator()(const std::vector<char>& path, size_t from,
		size_t to) const;
};

template<typename func> struct unary_builtin {
	const std::set<int_t> vals;
	const bool neg;
	const size_t bits;
	const sizes domain;
	const leq_const lt;
	const geq_const gt;

	std::set<int_t> get_vals(func f, size_t from, size_t to) const {
		std::set<int_t> r;
		for (; from != to; ++from) if (f(from)) r.insert(from);
		return r;
	}

	unary_builtin(const sizes& domain, bool neg, func f, size_t from,
		size_t to, size_t bits) : vals(get_vals(f, from, to)), neg(neg)
		, bits(bits), domain(domain), lt(domain, *vals.rbegin(), bits)
		, gt(domain, *vals.begin(), bits) {}

	builtin_res operator()(const std::vector<char>& path, size_t from,
		size_t to) const {
		builtin_res l = lt(path, from, to);
		if (l == FAIL) return neg ? PASS : FAIL;
		builtin_res g = gt(path, from, to);
		if (g == FAIL || (l == CONTLO && g == CONTHI))
			return neg ? PASS : FAIL;
		if (l == CONTLO) return CONTLO;
		if (g == CONTHI) return CONTHI;
		if (to - from <= bits) return CONTBOTH;
		int_t v = 0;
		for (size_t n = from; n != to; ++n)
			if (path[n] == 1)
				v |= (1 << (bits-n%bits-1));
			DBG(else assert(path[n]);)
		return	neg ? vals.find(v) != vals.end() ? PASS : FAIL :
			vals.find(v) == vals.end() ? PASS : FAIL;
	}
};
