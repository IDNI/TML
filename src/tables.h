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

//#ifndef __TABLES__
//#define __TABLES__

#include <map>
#include <vector>
#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#include <emscripten/val.h>
#endif
#include "bdd.h"
#include "term.h"
#include "bitsmeta.h"
#include "dict.h"
#include "infer_types.h"

typedef int_t rel_t;
struct raw_term;
struct raw_prog;
struct raw_rule;
struct raw_sof;
struct raw_form_tree;
class tables;
//class dict_t;

typedef std::pair<rel_t, ints> sig;
typedef std::map<int_t, size_t> varmap;
//typedef std::map<size_t, size_t> posmap;
typedef std::map<int_t, int_t> env;
typedef bdd_handles level;
//typedef std::set<std::vector<term>> flat_prog;

std::wostream& operator<<(std::wostream& os, const env& e);

template<typename T> struct ptrcmp {
	bool operator()(const T* x, const T* y) const { return *x < *y; }
};

typedef std::function<void(size_t,size_t,size_t, const std::vector<term>&)>
	cb_ground;


struct body {
	bool neg, ext = false;
//	struct alt *a = 0;
	ntable tab;
	bools ex;
	uints perm;
	spbdd_handle q, tlast, rlast;
	// TODO: to reinit get_perm on add_bit (well in the pfp/fwd), temp fix only.
	// (not sure how else to consistently perm from old bits perm to new one?)
	//ints vals;
	ints poss;
	// only for count, created on first use (rarely used)
	bools inv;
	//	static std::set<body*, ptrcmp<body>> &s;
	bool operator<(const body& t) const {
		if (q != t.q) return q < t.q;
		if (neg != t.neg) return neg;
		if (ext != t.ext) return ext;
		if (tab != t.tab) return tab < t.tab;
		if (ex != t.ex) return ex < t.ex;
		if (perm != t.perm) return perm < t.perm;
		//if (vals != t.vals) return vals < t.vals;
		return poss < t.poss;
	}
	bools init_perm_inv(size_t args) {
		inv = bools(args, false);
		// only count alt vars that are 'possible permutes' (of a body bit) 
		for (size_t i = 0; i < perm.size(); ++i)
			if (!ex[i]) inv[perm[i]] = true;
		return inv;
	}
};

struct table;

// TODO: make a proper move ctor for this, as alt is 'heavy' now, bm and all.

struct alt : public std::vector<body*> {
	spbdd_handle rng = htrue, eq = htrue, rlast = hfalse;
	size_t varslen;
	bdd_handles last;
	std::vector<term> t;
	bools ex;
	uints perm;
	varmap vm;
	std::map<size_t, int_t> inv;
	std::map<size_t, spbdd_handle> levels;
//	static std::set<alt*, ptrcmp<alt>> &s;
	int_t idbltin = -1;
	ints bltinargs;
	size_t bltinsize;
	bitsmeta bm;
	std::set<ntable> bodytbls; // map all b-s in alt, even if just consts

	bool operator<(const alt& a) const {
		if (varslen != a.varslen) return varslen < a.varslen;
		if (rng != a.rng) return rng < a.rng;
		if (eq != a.eq) return eq < a.eq;
		return (std::vector<body*>)*this<(std::vector<body*>)a;
	}
};

struct altpaircmp {
	bool operator()(
		const std::pair<alt, size_t>& x, const std::pair<alt, size_t>& y) const
	{
		return x.first < y.first;
	}
};
typedef std::set<std::pair<alt, size_t>, altpaircmp> alt_set;

struct rule : public std::vector<alt*> {
	bool neg;
	ntable tab;
	spbdd_handle eq, rlast = hfalse, h;
	size_t len;
	bdd_handles last;
	term t;
	bool operator<(const rule& r) const {
		if (neg != r.neg) return neg;
		if (tab != r.tab) return tab < r.tab;
		if (eq != r.eq) return eq < r.eq;
		return (std::vector<alt*>)*this < (std::vector<alt*>)r;
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
	size_t len, priority = 0;
	spbdd_handle tq = hfalse;
	bdd_handles add, del;
	std::vector<size_t> r;
	bool ext = true; // extensional
	bool unsat = false, tmp = false;
	int_t idbltin = -1;
	ints bltinargs;
	size_t bltinsize;
	bitsmeta bm;
	const dict_t& dict; // TODO: remove this dep., only needed for dict.nsyms()
	bool commit(DBG(size_t));
	spbdd_handle init_bits();
	//table() {}
	table(const sig& sg, size_t l, const dict_t& d) 
		: s(sg), len(l), tq{hfalse}, bm(l), dict(d) {}
};

struct form;
struct infer_types;

class tables {
	friend struct iterbdds;
	friend struct infer_types;
	friend std::ostream& operator<<(std::ostream& os, const tables& tbl);
	friend std::istream& operator>>(std::istream& is, tables& tbl);
public:
	typedef std::function<void(const raw_term&)> rt_printer;

	bool populate_tml_update = false;
	bool print_updates = false;
	bool print_steps = false;

private:
	typedef std::function<void(const term&)> cb_decompress;
	std::set<body*, ptrcmp<body>> bodies;
	std::set<alt*, ptrcmp<alt>> alts;

	nlevel nstep = 0;
	std::vector<table> tbls;
	std::set<ntable> tmprels;
	std::map<sig, ntable> smap;
	std::vector<rule> rules;
	std::vector<level> levels;
	std::map<ntable, std::set<ntable>> deps;
	std::map<ntable, std::set<tbl_alt>> tblbodies;
	std::map<ntable, std::set<term>> mhits;

	std::map<ntable, size_t> altids;

	// this is the real alts type info, used for post-processing e.g. addbit
	std::map<tbl_alt, alt*> altsmap;
	// maps tbl to rules
	std::map<ntable, std::set<size_t>> tblrules;
	// maps types (pre) ordering to (post) rules ordering (sorting is different)
	std::map<tbl_alt, tbl_alt> altordermap;

	// saved bin transform done during get_types (to reuse in get_rules)
	flat_prog pBin;

	// D: old stuff, just for historical reasons, and some comparing/debugging.
	//int_t _syms = 0, _nums = 0, _chars = 0;
	//size_t _bits = 2;

	dict_t dict;
	bool bproof, datalog, optimize, unsat = false, bcqc = true,
		 bin_transform = false, print_transformed, autotype = true, dumptype,
		 testaddbit, doemptyalts;

	size_t max_args = 0;
	std::map<std::array<int_t, 6>, spbdd_handle> range_memo;

	//	std::map<ntable, std::set<spbdd_handle>> goals;
	std::set<term> goals;
	std::set<ntable> to_drop;
	std::set<ntable> exts; // extensional
	strs_t strs;
	std::set<int_t> str_rels;
	flat_prog prog_after_fp; // prog to run after a fp (for cleaning nulls)
	//	std::function<int_t(void)>* get_new_rel;

	int_t rel_tml_update, sym_add, sym_del;

	infer_types inference;

	struct witness {
		size_t rl, al;
		std::vector<term> b;
		witness(size_t rl, size_t al, const std::vector<term>& b) :
			rl(rl), al(al), b(b) {}
		bool operator<(const witness& t) const {
			if (rl != t.rl) return rl < t.rl;
			if (al != t.al) return al < t.al;
			return b < t.b;
		}
	};

	struct proof_elem {
		size_t rl, al;
		std::vector<std::pair<nlevel, term>> b;
		bool operator<(const proof_elem& t) const {
			if (rl != t.rl) return rl < t.rl;
			if (al != t.al) return al < t.al;
			return b < t.b;
		}
	};

	typedef std::vector<std::map<term, std::set<proof_elem>>> proof;

	void print(std::wostream&, const proof_elem&);
	void print(std::wostream&, const proof&);
	void print(std::wostream&, const witness&);
	std::wostream& print(std::wostream& os, const std::vector<term>& b)
		const;
	std::wostream& print(std::wostream& os, const std::set<term>& b) const;
	std::wostream& print(std::wostream& os, const term& h,
		const std::set<term>& b) const;
	std::wostream& print(std::wostream& os, const flat_prog& p) const;
	std::wostream& print(std::wostream& os, const rule& r) const;

	void get_alt(
		const term_set& al, const term& h, alt_set& as, size_t altid);
	rule get_rule(const raw_rule&);
	
	template<typename T> void get_sym(
		int_t s, size_t n, size_t args, spbdd_handle& r, const T& at) const {
		return get_sym(s, n, args, r, at.bm);
	}
	void get_sym(
		int_t s, size_t n, size_t args, spbdd_handle& r, c_bitsmeta& bm) const;

	template<typename T> static void get_var_ex(
		size_t arg, size_t args, bools& vbs, const T& at) {
		return get_var_ex(arg, args, vbs, at.bm);
	}
	static void get_var_ex(
		size_t arg, size_t args, bools& vbs, c_bitsmeta& bm); // const;

	void get_alt_ex(alt& a, const term& h) const;
	void merge_extensionals();

	size_t arg(size_t v, size_t args) const {
		return v % args;
	}

	template<typename T> spbdd_handle from_sym(
		size_t arg, size_t args, int_t i, const T& altbl) const {
		return from_sym(arg, args, i, altbl.bm);
	}
	spbdd_handle from_sym(size_t arg, size_t args, int_t i, c_bitsmeta&) const;

	template<typename T> spbdd_handle from_sym_eq(
		size_t p1, size_t p2, size_t args, const T& altbl) const {
		return from_sym_eq(p1, p2, args, altbl.bm);
	}
	spbdd_handle from_sym_eq(
		size_t p1, size_t p2, size_t args, c_bitsmeta& bm) const;

	void init_bits();
	static xperm permex_add_bit(ints poss, c_bitsmeta& bm, c_bitsmeta& altbm);
	static perminfo add_bit_perm(bitsmeta& bm, size_t arg, size_t args);
	static spbdd_handle add_bit(
		spbdd_handle h, const perminfo& perm, size_t arg, size_t args);

	template<typename T> spbdd_handle leq_const(
		int_t c, size_t arg, size_t args, const T& altbl) const {
		return leq_const(c, arg, args, altbl.bm);
	}
	spbdd_handle leq_const(
		int_t c, size_t arg, size_t args, const bitsmeta& bm) const;
	spbdd_handle leq_const(int_t c, size_t arg, size_t args, size_t bit, 
		size_t bits, const bitsmeta& bm) const;

	template<typename T> spbdd_handle leq_var(
		size_t arg1, size_t arg2, size_t args, const T& at) const {
		return leq_var(arg1, arg2, args, at.bm);
	}
	spbdd_handle leq_var(size_t arg1, size_t arg2, size_t args,
		const bitsmeta& bm) const;
	spbdd_handle leq_var(size_t arg1, size_t arg2, size_t args, size_t bit, 
		const bitsmeta& bm) const;

	void range(size_t arg, size_t args, bdd_handles& v, const bitsmeta& bm) const;
	spbdd_handle range(size_t arg, ntable tab, const bitsmeta& bm);
	void range_clear_memo() { range_memo.clear(); }

	sig get_sig(const term& t);
	sig get_sig(const raw_term& t);
	sig get_sig(const lexeme& rel, const ints& arity);

	ntable add_table(sig s);

	static uints get_perm(
		const ints& poss, const bitsmeta& tblbm, const bitsmeta& altbm);
	uints get_perm(const term& t, const varmap& m, size_t len,
		const bitsmeta& tblbm, const bitsmeta& altbm) const;
	void init_varmap(alt& a, const term& h, const term_set& al);
	spbdd_handle get_alt_range(
		const term&, const term_set&, const varmap&, size_t len, const alt&);
	spbdd_handle get_alt_range(const term& h, const term_set& a,
		const varmap& vm, size_t len, const bitsmeta& bm);
	spbdd_handle from_term(const term&, body *b = 0,
		std::map<int_t, size_t>*m = 0, size_t hvars = 0);
	inline body get_body(const term&, const varmap&, size_t, const alt&) const;
	body get_body(
		const term& t, const varmap&, size_t len, const bitsmeta& bm) const;
//	void align_vars(std::vector<term>& b) const;
	spbdd_handle from_fact(const term& t);
	term from_raw_term(const raw_term&, bool ishdr = false, size_t orderid = 0);
	term to_tbl_term(sig s, ints t, argtypes types, ints nums, size_t nvars = 0,
		bool neg = false, term::textype extype=term::REL, bool realrel = true,
		lexeme rel=lexeme{0, 0}, t_arith_op arith_op = NOP, size_t orderid = 0);
	term to_tbl_term(ntable tab, ints t, argtypes types, ints nums, 
		size_t nvars = 0, bool neg = false, term::textype extype=term::REL,
		lexeme rel=lexeme{0, 0}, t_arith_op arith_op = NOP, size_t orderid = 0);
	
	static xperm deltail(const bitsmeta& abm, const bitsmeta& tblbm);
	xperm deltail(size_t args, size_t newargs,
		const bitsmeta& abm, const bitsmeta& tblbm) const;
	uints addtail(size_t len1, size_t len2, 
		const bitsmeta& tblbm, const bitsmeta& abm) const;
	spbdd_handle addtail(cr_spbdd_handle x, size_t len1, size_t len2,
		const bitsmeta& tblbm, const bitsmeta& abm) const;
	spbdd_handle body_query(body& b, size_t);
	spbdd_handle alt_query(alt& a, size_t);
	DBG(vbools allsat(spbdd_handle x, size_t args, const bitsmeta& bm) const;)
	void decompress(spbdd_handle x, ntable tab, const cb_decompress&,
		size_t len = 0, bool allowbltins = false) const;
	std::set<term> decompress();
	std::vector<env> varbdd_to_subs(const alt* a, cr_spbdd_handle v) const;
	void rule_get_grounds(cr_spbdd_handle& h, size_t rl, size_t level,
		cb_ground f);
	void term_get_grounds(const term& t, size_t level, cb_ground f);
	std::set<witness> get_witnesses(const term& t, size_t l);
	size_t get_proof(const term& q, proof& p, size_t level, size_t dep=-1);
	void run_internal_prog(flat_prog p, std::set<term>& r, size_t nsteps=0);
	ntable create_tmp_rel(size_t len, const argtypes& types, const ints& nums);
	void create_tmp_head(std::vector<term>& x, 
		std::vector<std::set<arg_info>>&, std::map<int_t, arg_info>&);
	//void getvars(const term&, std::set<arg_info>&);
	//void getvars(const std::vector<term>&, std::set<arg_info>&);
	void getvars(const term&, 
		std::vector<std::set<arg_info>>&, std::map<int_t, arg_info>&);
	void getvars(const std::vector<term>&, 
		std::vector<std::set<arg_info>>&, std::map<int_t, arg_info>&);
	void print_env(const env& e, const rule& r) const;
	void print_env(const env& e) const;
	struct elem get_elem(int_t arg, const arg_type& type) const;
	raw_term to_raw_term(const term& t) const;
	void out(std::wostream&, spbdd_handle, ntable) const;
	void out(spbdd_handle, ntable, const rt_printer&) const;
	void get_nums(const raw_term& t);
	flat_prog to_terms(const raw_prog& p);

	bool equal_types(const table& tbl, const alt& a) const;
	void get_rules(flat_prog m);
	void get_facts(const flat_prog& m);
	ntable get_table(const sig& s);
	void table_increase_priority(ntable t, size_t inc = 1);
	void set_priorities(const flat_prog&);
	ntable get_new_tab(int_t x, ints ar);
	lexeme get_new_rel();
	std::vector<ntable> init_string_tables(lexeme rel, const std::wstring& s);
	void load_string(
		lexeme rel, const std::wstring& s, const std::vector<ntable> tbls);
	// for loading 'facts', properly, if ever needed, leave it for now to test.
	//std::set<term> load_string(lexeme r, const std::wstring& s);
	lexeme get_var_lexeme(int_t i);
	void add_prog(flat_prog m, const std::vector<struct production>&,
		bool mknums = false);
	char fwd() noexcept;
	level get_front() const;
	std::vector<term> interpolate(
		std::vector<term>, std::set<arg_info>, const std::map<int_t, arg_info>&);
	//void transform_bin(flat_prog& p);
	flat_prog transform_bin(const flat_prog&);
	void transform_grammar(std::vector<struct production> g, flat_prog& p);
	bool cqc(const std::vector<term>& x, std::vector<term> y) const;
//	flat_prog cqc(std::vector<term> x, std::vector<term> y) const;
	bool cqc(const std::vector<term>&, const flat_prog& m) const;
	bool bodies_equiv(std::vector<term> x, std::vector<term> y) const;
	void cqc_minimize(std::vector<term>&) const;
	ntable prog_add_rule(flat_prog& p, std::map<ntable, ntable>& r,
		std::vector<term> x);

	// tml_update population
	void init_tml_update();
	void add_tml_update(const term& rt, bool neg);
	std::wostream& decompress_update(std::wostream& os, spbdd_handle& x,
		const rule& r); // decompress for --print-updates and tml_update

	bool from_raw_form(const raw_form_tree *rs, form *&froot);
	bool to_pnf( form *&froot);

	//-------------------------------------------------------------------------
	//XXX: arithmetic support, work in progress
	bool isarith_handler(const term& t, alt& a, ntable tab, spbdd_handle &leq);
	void set_constants(const term& t, alt& a, spbdd_handle &q, 
		const bitsmeta& bm) const;
	bitsmeta InitArithTypes(
		const term& t, const alt& a, ntable tab, size_t args) const;
	spbdd_handle leq_var(size_t arg1, size_t arg2, size_t args,
		size_t bit, spbdd_handle x, const bitsmeta& bm) const;
	spbdd_handle add_var_eq(size_t arg0, size_t arg1, size_t arg2, size_t args,
		const bitsmeta& bm) const;
	spbdd_handle full_addder_carry(size_t var0, size_t var1, size_t n_vars,
		uint_t b, spbdd_handle r, const bitsmeta& bm) const;
	spbdd_handle full_adder(size_t var0, size_t var1, size_t n_vars,
		uint_t b, const bitsmeta& bm) const;
	// D: turned off till it's fixed/reworked for var bits.
	//spbdd_handle shr(size_t var0, size_t n1, size_t var2, size_t n_vars);
	//spbdd_handle shl(size_t var0, size_t n1, size_t var2, size_t n_vars, 
	//	const bitsmeta& bm);
	//spbdd_handle full_addder_carry_shift(size_t var0, size_t var1, size_t n_vars,
	//	uint_t b, uint_t s, spbdd_handle r, const bitsmeta& bm) const;
	//spbdd_handle full_adder_shift(size_t var0, size_t var1, size_t n_vars,
	//	uint_t b, uint_t s, const bitsmeta& bm) const;
	//spbdd_handle add_ite(size_t var0, size_t var1, size_t args, uint_t b,
	//	uint_t s, const bitsmeta& bm);
	//spbdd_handle add_ite_init(size_t var0, size_t var1, size_t args, uint_t b,
	//	uint_t s);
	//spbdd_handle add_ite_carry(size_t var0, size_t var1, size_t args, uint_t b,
	//	uint_t s, const bitsmeta& bm);
	//spbdd_handle mul_var_eq(size_t var0, size_t var1, size_t var2,
	//			size_t n_vars);
	//spbdd_handle mul_var_eq_ext(size_t var0, size_t var1, size_t var2,
	//	size_t var3, size_t n_vars);
	//spbdd_handle bdd_test(size_t n_vars);
	//spbdd_handle bdd_add_test(size_t n_vars);
	//spbdd_handle bdd_mult_test(size_t n_vars);
	uints get_perm_ext(const term& t, const varmap& m, size_t len, 
		const bitsmeta& tblbm, const bitsmeta& abm) const;

	//spbdd_handle ex_typebits(size_t in_varid, spbdd_handle in, size_t n_vars);
	//spbdd_handle perm_from_to(size_t from, size_t to, spbdd_handle in, size_t n_bits, size_t n_vars);
	//spbdd_handle perm_bit_reverse(spbdd_handle in,  size_t n_bits, size_t n_vars);
	//spbdd_handle bitwise_handler(size_t in0_varid, size_t in1_varid, size_t out_varid,
	//		spbdd_handle in0, spbdd_handle in1, size_t n_vars, t_arith_op op);
	//spbdd_handle pairwise_handler(size_t in0_varid, size_t in1_varid, size_t out_varid,
	//		spbdd_handle in0, spbdd_handle in1, size_t n_vars, t_arith_op op);

	//t_arith_op get_bwop(lexeme l);
	//t_arith_op get_pwop(lexeme l);

public:
	tables(dict_t dict, bool bproof = false, bool optimize = true,
		bool bin_transform = false, bool print_transformed = false,
		bool autotype = true, bool dumptype = false, bool addbit = false,
		bool bitsfromright = true);
	~tables();
	size_t step() { return nstep; }
	void add_prog(const raw_prog& p, const strs_t& strs);
	bool run_prog(const raw_prog& p, const strs_t& strs, size_t steps = 0,
		size_t break_on_step = 0);
	bool run_nums(flat_prog m, std::set<term>& r, size_t nsteps);
	bool pfp(size_t nsteps = 0, size_t break_on_step = 0);
	void out(std::wostream&) const;
	void out(const rt_printer&) const;
#ifdef __EMSCRIPTEN__
	void out(emscripten::val o) const;
#endif
	void set_proof(bool v) { bproof = v; }
	bool get_goals(std::wostream& os);
	dict_t& get_dict() { return dict; }

	std::wostream& print_dict(std::wostream& os) const;
};

struct transformer;
struct form{
friend struct transformer;

	int_t arg;
	term *tm;
	form *l;
	form *r;
	enum ftype { NONE, ATOM, FORALL1, EXISTS1, FORALL2, EXISTS2, UNIQUE1, UNIQUE2, AND, OR, NOT, IMPLIES, COIMPLIES
	} type;


	form(){
		type = NONE; l = NULL; r = NULL; arg = 0; tm = NULL;
	}

	form( ftype _type, int_t _arg=0, term *_t=NULL, form *_l= NULL, form *_r=NULL  ) {
		arg= _arg; tm = _t; type = _type; l = _l; r = _r;
		if( _t) tm = new term(), *tm = *_t;
	}
	bool isquantifier() const {
		 if( type == form::ftype::FORALL1 ||
			 type == form::ftype::EXISTS1 ||
			 type == form::ftype::UNIQUE1 ||
			 type == form::ftype::EXISTS2 ||
			 type == form::ftype::UNIQUE2 ||
			 type == form::ftype::FORALL2 )
			 return true;
		return false;

	}

	~form() {
		if(l) delete l, l = NULL;
		if(r) delete r, r = NULL;
		if(tm) delete tm, tm = NULL;
	}
	void printnode(int lv=0);
};

struct transformer {
	virtual bool apply(form *&root) = 0;
	form::ftype getdual( form::ftype type);
	virtual bool traverse(form *&);
};


struct implic_removal : public transformer {

	 virtual bool apply(form *&root);
};

struct demorgan : public transformer {


	bool allow_neg_move_quant =false;
	bool push_negation( form *&root);
	virtual bool apply( form *&root);
	demorgan(bool _allow_neg_move_quant =false){
		allow_neg_move_quant = _allow_neg_move_quant;
	}
};

struct pull_quantifier: public transformer {
	dict_t &dt;
	pull_quantifier(dict_t &_dt): dt(_dt) {}
	virtual bool apply( form *&root);
	virtual bool traverse( form *&root);
	bool dosubstitution(form * phi, form* end);
};
struct substitution: public transformer {

	std::map<int_t, int_t> submap_var;
	std::map<int_t, int_t> submap_sym;

	void clear() { submap_var.clear(); submap_sym.clear();}
	void add( int_t oldn, int_t newn) {
		if(oldn < 0)
			submap_var[oldn] = newn;
		else
			submap_sym[oldn] = newn;
	}

	virtual bool apply(form *&phi);

};

std::wostream& operator<<(std::wostream& os, const vbools& x);

struct unsat_exception : public std::exception {
	virtual const char* what() const noexcept { return "unsat."; }
};

struct contradiction_exception : public unsat_exception {
	virtual const char* what() const noexcept {
		return "unsat (contradiction).";
	}
};

struct infloop_exception : public unsat_exception {
	virtual const char* what() const noexcept {
		return "unsat (infinite loop).";
	}
};

//#endif
