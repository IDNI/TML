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
	const sizes domain;
	std::vector<char> path;
	sizes getdom() const;
	std::unordered_map<size_t, size_t> memo;
	size_t compute(size_t x, size_t v);
public:
	bdd_and_eq(size_t bits, const term& t);
	size_t operator()(size_t x);
};

enum builtin_res { PASS, FAIL, CONTHI, CONTLO, CONTBOTH };
template<typename T> T sort(const T& x);
#define has(x, y) std::binary_search(x.begin(), x.end(), y)
#define del(x, y) x.erase(std::equal_range(x.begin(), x.end(), y).first)

template<typename func> class builtins {
	const size_t bits, nvars, tail;
	sizes domain;
	std::vector<char> path;
	sizes getdom() const;
	int_t get_int(size_t pos) const;
	std::unordered_map<size_t, size_t> memo;
	func f;

	size_t compute(size_t x, size_t v) {
		if (leaf(x) && (!trueleaf(x) || v == nvars)) return x;
		node n = getnode(x);
		if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
		assert(v<nvars);
		if (!has(domain, v/bits))
			return	++v, bdd_add({{v, compute(n[1], v),
				compute(n[2], v)}});
		switch (f(path, (v/bits)*bits, v)) {
			case FAIL: return F;
			case CONTHI:return bdd_add({{v+1,compute(n[1],v+1),F}});
			case CONTLO:return bdd_add({{v+1,F,compute(n[2],v+1)}});
			case PASS: del(domain, v/bits);
			default: ;
		}
		return	path[v] = 1, x = compute(n[1], v+1), path[v++] = -1,
			bdd_add({{v, x, compute(n[2], v)}});
	}
public:
	builtins(size_t bits, size_t nvars, size_t tail, func f) : bits(bits)
		, nvars(nvars), tail(tail), domain(sort(f.domain))
		, path(nvars,0), f(f) {}

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
		, domain(domain) {}
	builtin_res operator()(const std::vector<char>& path, size_t from,
		size_t to) const;
};
