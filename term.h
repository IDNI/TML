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

struct term {
	bool neg;
	int_t rel;
	ints args, arity;
	term () {}
	term(bool neg, int_t rel) : neg(neg), rel(rel) {}
	term(bool neg, int_t rel, const ints& args,
		const ints& arity) : neg(neg), rel(rel)
		, args(args), arity(arity) {}
	bool operator<(const term& t) const {
		if (neg != t.neg) return neg;
		if (rel != t.rel) return rel < t.rel;
		if (arity != t.arity) return arity < t.arity;
		return args < t.args;
	}
};

typedef std::vector<size_t> sizes;
typedef std::vector<term> matrix;
typedef std::set<matrix> matrices;
typedef std::set<std::pair<matrix, matrix>> matpairs;
std::wostream& operator<<(std::wostream& os, const term& t);
std::wostream& operator<<(std::wostream& os, const matrix& m);
std::wostream& operator<<(std::wostream& os, const matrices& m);
