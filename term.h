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

class term {
	bool _neg;
	int_t _rel;
	ints _args, _arity;
public:
	term () {}
	term(bool neg, int_t rel) : _neg(neg), _rel(rel) {}
	term(bool neg, int_t rel, const ints& args,
		const ints& arity) : _neg(neg), _rel(rel)
		, _args(args), _arity(arity) {}
	bool neg() const { return _neg; }
	int_t rel() const { return _rel; }
	const ints& args() const { return _args; }
	const ints& arity() const { return _arity; }
	int_t& arg(size_t n) { return _args[n]; }
	const int_t& arg(size_t n) const { return _args[n]; }
	void setrel(int_t r) { _rel = r; }
	void setneg(bool b) { _neg = b; }
	void add_arg(int_t x) { _args.push_back(x); }
	void set_arity(const ints& a) { _arity = a; }
	size_t nargs() const { return _args.size(); }
	bool operator<(const term& t) const {
		if (_neg != t._neg) return _neg;
		if (_rel != t._rel) return _rel < t._rel;
		if (_arity != t._arity) return _arity < t._arity;
		return _args < t._args;
	}
};

typedef std::vector<size_t> sizes;
typedef std::vector<term> matrix;
typedef std::set<matrix> matrices;
typedef std::set<std::pair<matrix, matrix>> matpairs;
std::wostream& operator<<(std::wostream& os, const term& t);
std::wostream& operator<<(std::wostream& os, const matrix& m);
std::wostream& operator<<(std::wostream& os, const matrices& m);
