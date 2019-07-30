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
#include "term.h"

typedef int_t rel_t;
struct raw_term;
struct raw_prog;
struct raw_rule;
class tables;
class dict_t;

typedef std::pair<rel_t, ints> sig;
typedef std::map<int_t, size_t> varmap;
typedef bdd_handles level;

std::map<int_t, int_t> cqc(term h1, std::vector<term> b1, term h2,
	std::vector<term> b2);

template<typename T> struct ptrcmp {
	bool operator()(const T* x, const T* y) const { return *x < *y; }
};

struct body {
	bool neg, ext = false;
	struct alt *a = 0;
	ntable tab;
	bools ex;
	uints perm;
	spbdd_handle q, tlast, rlast;
	static std::set<body*, ptrcmp<body>> s;
	bool operator<(const body& t) const {
		if (q != t.q) return q < t.q;
		if (neg != t.neg) return neg;
		if (ext != t.ext) return ext;
		if (tab != t.tab) return tab < t.tab;
		if (ex != t.ex) return ex < t.ex;
		return perm < t.perm;
	}
};

struct alt : public std::vector<body*> {
	spbdd_handle rng = bdd_handle::T, rlast = bdd_handle::F;
	size_t varslen;
	bdd_handles last;
	std::vector<term> t;
	bools ex;
	uints perm;
	varmap vm;
	std::map<size_t, int_t> inv;
	static std::set<alt*, ptrcmp<alt>> s;
	bool operator<(const alt& t) const {
		if (varslen != t.varslen) return varslen < t.varslen;
		if (rng != t.rng) return rng < t.rng;
		return (std::vector<body*>)*this<(std::vector<body*>)t;
	}
};

struct rule : public std::vector<alt*> {
	bool neg;
	ntable tab;
	spbdd_handle eq, rlast = bdd_handle::F, h;
	size_t len;
	bdd_handles last;
	term t;
	bool operator<(const rule& t) const {
		if (neg != t.neg) return neg;
		if (tab != t.tab) return tab < t.tab;
		if (eq != t.eq) return eq < t.eq;
		return (std::vector<alt*>)*this < (std::vector<alt*>)t;
	}
	bool equals_termwise(const rule& r) const {
		if (t != r.t || size() != r.size()) return false;
		for (size_t n = 0; n != size(); ++n)
			if (at(n)->t != r[n]->t) return false;
		return true;
	}
};

struct table {
	sig s;
	size_t len;
	spbdd_handle t = bdd_handle::F;
	bdd_handles add, del;
	bool ext = true; // extensional
	bool commit(DBG(size_t));
};

class tables {
	typedef std::function<void(const raw_term&)> rt_printer;
	typedef std::function<void(const term&)> cb_decompress;

	std::vector<table> ts;
	std::map<sig, ntable> smap;
	std::vector<rule> rules;
	alt get_alt(const std::vector<raw_term>&);
	rule get_rule(const raw_rule&);
	void get_sym(int_t s, size_t arg, size_t args, spbdd_handle& r) const;
	void get_var_ex(size_t arg, size_t args, bools& b) const;
	void get_alt_ex(alt& a, const term& h) const;
	void merge_extensionals();

	int_t syms = 0, nums = 0, chars = 0;
	size_t bits = 2;
	dict_t& dict;
	bool datalog, optimize;

	size_t max_args = 0;
	std::map<std::array<int_t, 6>, spbdd_handle> range_memo;

	size_t pos(size_t bit, size_t nbits, size_t arg, size_t args) const {
		DBG(assert(bit < nbits && arg < args);)
		return (nbits - bit - 1) * args + arg;
	}

	size_t pos(size_t bit_from_right, size_t arg, size_t args) const {
		DBG(assert(bit_from_right < bits && arg < args);)
		return (bits - bit_from_right - 1) * args + arg;
	}

	size_t arg(size_t v, size_t args) const {
		return v % args;
	}

	size_t bit(size_t v, size_t args) const {
		return bits - 1 - v / args;
	}

	spbdd_handle from_bit(size_t b, size_t arg, size_t args, int_t n) const{
		return ::from_bit(pos(b, arg, args), n & (1 << b));
	}
	spbdd_handle from_sym(size_t pos, size_t args, int_t i) const;
	spbdd_handle from_sym_eq(size_t p1, size_t p2, size_t args) const;

	void add_bit();
	spbdd_handle add_bit(spbdd_handle x, size_t args);
	spbdd_handle leq_const(int_t c, size_t arg, size_t args, size_t bit)
		const;
	void range(size_t arg, size_t args, bdd_handles& v);
	spbdd_handle range(size_t arg, ntable tab);
	void range_clear_memo() { range_memo.clear(); }

	sig get_sig(const raw_term& t);
	ntable add_table(sig s);
	uints get_perm(const term& t, const varmap& m, size_t len) const;
	template<typename T>
	static varmap get_varmap(const term& h, const T& b, size_t &len);
	spbdd_handle get_alt_range(const term& h, const std::set<term>& a,
			const varmap& vm, size_t len);
	spbdd_handle from_term(const term&, body *b = 0,
		std::map<int_t, size_t>*m = 0, size_t hvars = 0);
	body get_body(const term& t, const varmap&, size_t len) const;
	void align_vars(term& h, std::set<term>& b) const;
	spbdd_handle from_fact(const term& t);
	term from_raw_term(const raw_term&);
	std::pair<bools, uints> deltail(size_t len1, size_t len2) const;
	spbdd_handle body_query(body& b, size_t);
	spbdd_handle alt_query(alt& a, size_t);
	DBG(vbools allsat(spbdd_handle x, size_t args) const;)
	void decompress(spbdd_handle x, ntable tab, const cb_decompress&,
		size_t len = 0) const;
	std::set<term> decompress();
	std::map<int_t, int_t> varbdd_to_subs(const alt* a, cr_spbdd_handle v)
		const;
	void bwd_facts(const bdd_handles& v, std::map<term, std::set<term>>& m);
	raw_term to_raw_term(const term& t) const;
	void out(std::wostream&, spbdd_handle, ntable) const;
	void out(spbdd_handle, ntable, const rt_printer&) const;
	std::map<term, std::set<std::set<term>>> to_terms(const raw_prog& p);
	void get_rules(const std::map<term, std::set<std::set<term>>>& m);
	void get_facts(const std::map<term, std::set<std::set<term>>>& m);
	ntable get_table(const sig& s);
	void load_string(lexeme rel, const std::wstring& s);
	void add_prog(const raw_prog& p, const strs_t& strs);
	void add_prog(std::map<term, std::set<std::set<term>>> m,
		const strs_t& strs, bool mknums = false);
	char fwd();
	level get_front() const;
	std::map<ntable, std::set<spbdd_handle>> goals;
	std::set<ntable> to_drop;
public:
	tables(bool optimize = true);
	~tables();
	bool run_prog(const raw_prog& p, const strs_t& strs);
	bool run_nums(const std::map<term, std::set<std::set<term>>>& m,
		std::set<term>& r);
	bool pfp(std::vector<level>* v = 0);
	void out(std::wostream&) const;
	void out(const rt_printer&) const;
};

std::wostream& operator<<(std::wostream& os, const vbools& x);
