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
#include <map>
#include <vector>
#include "bdd.h"

typedef int_t ntable;
typedef int_t rel_t;
struct raw_term;
struct raw_prog;
struct raw_rule;
class tables;
class dict_t;

typedef std::pair<rel_t, ints> sig_t;

class tables {
private:
	typedef std::map<int_t, size_t> varmap;
	struct term : public ints {
		bool neg;//, eq;
		ntable tab;
//		ints &args;
		term();//: /*eq(false), */args(*this) {}
		term(bool neg, ntable tab, const ints& args) :
			ints(args), neg(neg), /*eq(false),*/ tab(tab){}//, args(*this){}
//		term(int_t t) : // table equality
//			ints({t}), eq(true), neg(false), args(*this) {}
//		term(bool neg, int_t x, int_t y) : // var/const equality
//			ints({x, y}), eq(true), neg(neg), args(*this) {}
		bool operator<(const term& t) const {
			if (neg != t.neg) return neg;
			if (tab != t.tab) return tab < t.tab;
			return (const ints&)*this < t;
		}
//		int_t operator[](size_t n) const { return args[n]; }
//		int_t& operator[](size_t n) { return args[n]; }
		void replace(const std::map<int_t, int_t>& m);
	};
	struct body {
		bool neg;
		ntable tab;
		bools ex;
		sizes perm;
		spbdd q;
		bool operator<(const body& t) const {
			if (q != t.q) return q < t.q;
			if (neg != t.neg) return neg;
			if (tab != t.tab) return tab < t.tab;
			if (ex != t.ex) return ex < t.ex;
			return perm < t.perm;
		}
	};
	struct alt {
		spbdd rng;//, eq;
		size_t varslen;
		std::set<body> b;
		bool operator<(const alt& t) const {
//			if (eq != t.eq) return eq < t.eq;
			if (rng != t.rng) return rng < t.rng;
			return b < t.b;
		}
	};
	struct rule {
		bool neg;
		ntable tab;
		spbdd eq, rng;
		std::set<alt> alts;
		bool operator<(const rule& t) const {
			if (neg != t.neg) return neg;
			if (tab != t.tab) return tab < t.tab;
			if (eq != t.eq) return eq < t.eq;
			if (rng != t.rng) return rng < t.rng;
			return alts < t.alts;
		}
	};
	alt get_alt(const std::vector<raw_term>&);
	rule get_rule(const raw_rule&);

	int_t syms = 0, nums = 0, chars = 0;
	size_t bits = 2, tbits = 0; // #bits for elem, #bits for table id
	dict_t& dict;

	std::map<sig_t, ntable> ts;
	std::vector<sig_t> sigs;
	std::vector<size_t> siglens;
	bdds tbdds;
	size_t max_args = 0;
	std::map<std::array<int_t, 7>, spbdd> range_memo;

	spbdd db = F;

	size_t pos(size_t bit, size_t nbits, size_t arg, size_t args) const {
		DBG(assert(bit < nbits && args <= max_args && arg < args);)
		return (nbits - bit - 1) * args + arg + tbits;
	}

	size_t pos(size_t bit_from_right, size_t arg, size_t args) const {
		DBG(assert(bit_from_right<bits && args<=max_args && arg<args);)
		return (bits - bit_from_right - 1) * args + arg + tbits;
	}

	size_t arg(size_t v, size_t args) const {
		DBG(assert(v >= tbits);)
		return (v - tbits) % args;
	}

	size_t bit(size_t v, size_t args) const {
		DBG(assert(v >= tbits);)
		return bits - 1 - (v - tbits) / args;
	}

	spbdd from_bit(size_t b, size_t arg, size_t args, int_t n) const {
		return bdd::from_bit(pos(b, arg, args), n & (1 << b));
	}

	void add_bit();
	spbdd add_bit(spbdd x, ntable tab);
	void add_tbit();
	spbdd leq_const(int_t c, size_t arg, size_t args, size_t bit) const;
	void range(size_t arg, size_t args, bdds& v);
	spbdd range(size_t arg, ntable tab);
	void range_clear_memo() {onmemo(-range_memo.size()),range_memo.clear();}

	sig_t get_sig(const raw_term& t);
	ntable add_table(sig_t s);
	ntable get_table(const raw_term& t);
	sizes get_perm(const term& t, const varmap& m, size_t len) const;
	static varmap get_varmap(const term& h, const std::set<term>& b,
		size_t &len);
	spbdd get_alt_range(const term& h, const std::set<term>& a,
			const varmap& vm, size_t len);
	spbdd from_term(const term&, body *b = 0, std::map<int_t, size_t>*m = 0,
		size_t hvars = 0);
	body get_body(const term& t, const varmap&, size_t len) const;
	std::set<rule> get_rules(const raw_prog& p);
	void align_vars(term& h, std::set<term>& b) const;
	spbdd from_fact(const term& t);
	void add_term(const term& t);
	term from_raw_term(const raw_term&);
	DBG(vbools allsat(spbdd x, ntable tab);)
	void validate();
public:
//	typedef std::map<item, std::set<std::set<item>>> transaction;
	tables();
	~tables();
	void add_raw_terms(const std::vector<raw_term>& rows);
	std::map<term, std::set<std::set<term>>> to_terms(const raw_prog& p);
	void add_prog(const raw_prog& p);
	void fwd();
	void pfp();
	void out(std::wostream&);
};
