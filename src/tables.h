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
		bool neg;
		ntable tab;
		term(bool neg, ntable tab, const ints& args) :
			ints(args), neg(neg), tab(tab) {}
		bool operator<(const term& t) const {
			if (neg != t.neg) return neg;
			if (tab != t.tab) return tab < t.tab;
			return (const ints&)*this < t;
		}
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
	struct alt : public std::vector<body> {
		spbdd rng;
		size_t varslen;
		bool operator<(const alt& t) const {
			if (varslen != t.varslen) return varslen < t.varslen;
			if (rng != t.rng) return rng < t.rng;
			return (std::vector<body>)*this < (std::vector<body>)t;
		}
	};
	struct rule : public std::vector<alt> {
		bool neg;
		ntable tab;
		spbdd eq;
		size_t len;
		std::set<alt> alts;
		bool operator<(const rule& t) const {
			if (neg != t.neg) return neg;
			if (tab != t.tab) return tab < t.tab;
			if (eq != t.eq) return eq < t.eq;
			return (std::vector<alt>)*this < (std::vector<alt>)t;
		}
	};
	std::vector<rule> rules;
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
	spbdd get_table(ntable tab, spbdd x) const;
	sizes get_perm(const term& t, const varmap& m, size_t len) const;
	static varmap get_varmap(const term& h, const std::set<term>& b,
		size_t &len);
	spbdd get_alt_range(const term& h, const std::set<term>& a,
			const varmap& vm, size_t len);
	spbdd from_term(const term&, body *b = 0, std::map<int_t, size_t>*m = 0,
		size_t hvars = 0);
	body get_body(const term& t, const varmap&, size_t len) const;
	void align_vars(term& h, std::set<term>& b) const;
	void count_term(const raw_term& t);
	spbdd from_fact(const term& t);
	void add_term(const term& t);
	term from_raw_term(const raw_term&);
	spbdd deltail(spbdd x, size_t len1, size_t len2) const;
	spbdd body_query(const body& b) const;
	void alt_query(const alt& a, size_t len, bdds& v) const;
	DBG(vbools allsat(spbdd x, ntable tab);)
	void validate();
public:
	tables();
	~tables();
	void get_rules(const raw_prog& p);
	void add_prog(const raw_prog& p);
	void fwd();
	void pfp();
	void out(std::wostream&);
};
