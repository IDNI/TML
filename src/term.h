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

struct prefix {
	int_t rel;
	ints ar;

	prefix() {}
	prefix(int_t rel, const ints& ar) : rel(rel), ar(ar) {}

	size_t len() const {
		size_t r = 0;
		for (auto x : ar) if (x > 0) r += x;
		return r;
	}

	std::vector<std::pair<ints, std::array<size_t, 2>>> subterms() const {
		assert(ar.size() && ar[0] == 0);
		std::vector<std::pair<ints, std::array<size_t, 2>>> r;
		for (size_t n=1, from=0, last=0, dep=0; n != ar.size(); ++n) {
			if (ar[n] == -1) { if (!dep++) from = 0; }
			else if (ar[n] != -2) from += ar[n];
			else if (!--dep)
				r.push_back({{}, {last,last+from}}), last=from;
		}
		size_t k = 0;
		ints x = {0};
		for (size_t n = ar[0]==0 ? 1 : 0, dep = 0; n != ar.size(); ++n)
			if (x.push_back(ar[n]), ar[n] == -1) dep++;
			else if (ar[n] == -2 && !--dep) r[k++].first = x, x={0};
		return r;
	}

	bool operator<(const prefix& t) const {
		return rel != t.rel ? rel < t.rel : ar < t.ar;
	}

	bool operator==(const prefix& t) const { return rel==t.rel&&ar==t.ar; }
	bool operator!=(const prefix& t) const { return rel!=t.rel||ar!=t.ar; }
};

/*template<> struct std::hash<prefix> {
	size_t operator()() const {
		static std::hash<bool> h1;
		static std::hash<int_t> h2;
		static std::hash<ints> h3;
		return h1(neg) + h2(rel) + h3(ar);
	}
};*/

class term {
	bool _neg;
	ints _args;
	prefix p;
public:
	term () {}
	term(bool neg, int_t rel) : _neg(neg), p(rel, {}) {}
	term(bool neg, int_t rel, const ints& args, const ints& arity)
		: _neg(neg), _args(args), p(rel, arity) {}
	term(bool neg, const ints& args, const prefix& p)
		: _neg(neg), _args(args), p(p) {}
	bool neg() const { return _neg; }
	int_t rel() const { return p.rel; }
	const ints& args() const { return _args; }
	const ints& arity() const { return p.ar; }
	const prefix& pref() const { return p; }
	int_t& arg(size_t n) { return _args[n]; }
	const int_t& arg(size_t n) const { return _args[n]; }
	void setrel(int_t r) { p.rel = r; }
	void setneg(bool b) { _neg = b; }
	void add_arg(int_t x) { _args.push_back(x); }
	void set_arity(const ints& a) { p.ar = a; }
	size_t nargs() const { return _args.size(); }
	bool operator<(const term& t) const {
		return _neg==t._neg ? p==t.p ? _args < t._args : p < t.p : _neg;
	}
};

typedef std::vector<term> matrix;
typedef std::set<matrix> matrices;
typedef std::set<std::pair<matrix, matrix>> matpairs;
std::wostream& operator<<(std::wostream& os, const term& t);
std::wostream& operator<<(std::wostream& os, const matrix& m);
std::wostream& operator<<(std::wostream& os, const matrices& m);
#endif
