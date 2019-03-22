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

class query {
	const bool neg;
	const size_t bits, nvars;
	const std::vector<int_t> e;
	std::vector<size_t> perm;
	const std::set<size_t> s;
	std::vector<char> path;
	std::set<size_t> get_s() const;
	static std::vector<int_t> from_term(const term& t);
public:
	query(size_t bits, const term& t, const std::vector<size_t>& perm);
	size_t operator()(size_t x, size_t v = 0);
};

class extents {
	const size_t bits, nvars, tail;
	const int_t glt, ggt;
	const std::vector<int_t> excl, lt, gt;
	const std::set<size_t> s;
	bools path;
	std::set<size_t> get_s() const;
	int_t get_int(size_t pos) const;
public:
	// excl must be sorted
	extents(size_t bits, size_t ar, size_t tail, int_t glt, int_t ggt,
		const std::vector<int_t>& excl, const std::vector<int_t>& lt,
		const std::vector<int_t>& gt);
	size_t operator()(size_t x, size_t v = 0);
};
