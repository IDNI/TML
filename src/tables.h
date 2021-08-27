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
#include "dict.h"
#include "input.h"
#include "form.h"
#include "err.h"
#include "options.h"
#include "builtins.h"
#include "analysis.h"
#include "ir_builder.h"

typedef bdd_handles level;

class archive;
class tables;

struct body {
	bool neg = false;
	ntable tab;
	bools ex;
	uints perm;
	spbdd_handle q, tlast, rlast;
	// only for count, created on first use (rarely used)
	bools inv;
	bool operator<(const body& t) const {
		if (q != t.q) return q < t.q;
		if (neg != t.neg) return neg;
		if (tab != t.tab) return tab < t.tab;
		if (ex != t.ex) return ex < t.ex;
		return perm < t.perm;
	}
	bools init_perm_inv(size_t args) {
		bools inv(args, false);
		// only count alt vars that are 'possible permutes' (of a body bit)
		for (size_t i = 0; i < perm.size(); ++i)
			if (!ex[i]) inv[perm[i]] = true;
		return inv;
	}
};

struct alt : public std::vector<body*> {
	spbdd_handle rng = htrue, eq = htrue, rlast = hfalse;
	size_t varslen = 0;
	bdd_handles last;
	std::optional<int_t> rule_id;
	std::vector<term> t;
	std::vector<term> bltins; // builtins to run during alt_query
	bools ex;
	uints perm;
	varmap vm;
	std::map<size_t, int_t> inv;
	std::map<size_t, spbdd_handle> levels;

	alt* grnd = 0; // alt for grounding vars
	std::set<int_t> bltinvars;  // vars to ground
	std::set<int_t> bltngvars;  // vars to keep ungrounded (ie. count, bw_/pw_)
	std::set<int_t> bltoutvars; // vars for outputs to compress
	std::set<std::pair<int_t, body*>> varbodies;

	pnft_handle f = 0;

	bool operator<(const alt& t) const {
		if (varslen != t.varslen) return varslen < t.varslen;
		if (rng != t.rng) return rng < t.rng;
		if (eq != t.eq) return eq < t.eq;
		if (f != t.f) return f < t.f;
		if (ex != t.ex) return ex < t.ex;
		if (perm != t.perm) return perm < t.perm;
		if (bltins != t.bltins) return bltins < t.bltins;
		if (grnd != t.grnd) return grnd < t.grnd;
		if (bltinvars != t.bltinvars) return bltinvars < t.bltinvars;
		if (bltngvars != t.bltngvars) return bltngvars < t.bltngvars;
		if (bltoutvars != t.bltoutvars) return bltoutvars <t.bltoutvars;
		if (varbodies != t.varbodies) return varbodies <t.varbodies;
		return (std::vector<body*>)*this<(std::vector<body*>)t;
	}
};

struct rule : public std::vector<alt*> {
	bool neg;
	ntable tab;
	spbdd_handle eq, rlast = hfalse, h;
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
	size_t len, priority = 0;
	spbdd_handle t = hfalse;
	bdd_handles add, del;
	std::vector<size_t> r;
	bool unsat = false, tmp = false;
	int_t idbltin = -1;
	ints bltinargs;
	size_t bltinsize = 0;
	bool hidden = false;
	// The ID of the table that instruments this rule
	std::optional<int_t> instr_tab;
	bool commit(DBG(size_t));
	inline bool is_builtin() const { return idbltin > -1; }
};

class tables {
	friend class archive;
	friend std::ostream& operator<<(std::ostream& os, const tables& tbl);
	friend std::istream& operator>>(std::istream& is, tables& tbl);
	friend struct form;
	friend struct pnft;
	friend struct term;
	friend class ir_builder;
	friend class driver;
	friend class bit_univ;

public:
	typedef std::function<void(const raw_term&)> rt_printer;

private:
	typedef int_t rel_t;

	typedef std::function<void(size_t,size_t,size_t, const std::vector<term>&)>
		cb_ground;
	typedef std::function<void(const term&)> cb_decompress;
	std::set<body*, ptrcmp<body>> bodies;
	std::set<alt*, ptrcmp<alt>> alts;
	//std::set<alt*, ptrcmp<alt>> grnds;
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

	nlevel nstep = 0;
	std::vector<table> tbls;
	std::map<sig, ntable> smap;
	std::vector<rule> rules;
	std::vector<level> fronts;
	std::vector<level> levels;

	void get_sym(int_t s, size_t arg, size_t args, spbdd_handle& r) const;
	void get_var_ex(size_t arg, size_t args, bools& b) const;
	void get_alt_ex(alt& a, const term& h) const;
	int_t freeze(std::vector<term>& v, int_t );
	std::vector<term> to_nums(const std::vector<term>& v);
	void to_nums(flat_prog& m);
	term to_nums(term t);
	flat_prog& get_canonical_db(std::vector<term>& x, flat_prog& p);
	flat_prog& get_canonical_db(std::vector<std::vector<term>>& x, flat_prog& p);

	size_t bits = 2;/*TODO: this init is affecting dict.cpp:36*/
	dict_t& dict;
	bool datalog, halt = false, unsat = false, bcqc = false;
	size_t max_args = 0;

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
	spbdd_handle leq_var(size_t arg1, size_t arg2, size_t args) const;
	spbdd_handle leq_var(size_t arg1, size_t arg2, size_t args, size_t bit)
		const;


	ntable add_table(sig s);
	uints get_perm(const term& t, const varmap& m, size_t len) const;
	uints get_perm(const term& t, const varmap& m, size_t len, size_t bits) const;
	template<typename T>
	static varmap get_varmap(const term& h, const T& b, size_t &len,
		bool blt = false);

	spbdd_handle from_term(const term&, body *b = 0,
		std::map<int_t, size_t>*m = 0, size_t hvars = 0);
	body get_body(const term& t, const varmap&, size_t len) const;
//	void align_vars(std::vector<term>& b) const;
	spbdd_handle from_fact(const term& t);

	std::pair<bools, uints> deltail(size_t len1, size_t len2) const;
	std::pair<bools, uints> deltail(size_t len1, size_t len2, size_t bits) const;
	uints addtail(size_t len1, size_t len2) const;
	spbdd_handle addtail(cr_spbdd_handle x, size_t len1, size_t len2) const;
	spbdd_handle body_query(body& b, size_t);
	spbdd_handle alt_query(alt& a, size_t);

	DBG(vbools allsat(spbdd_handle x, size_t args) const;)
	void decompress(spbdd_handle x, ntable tab, const cb_decompress&,
		size_t len = 0, bool allowbltins = false) const;
	std::set<term> decompress();
	std::vector<env> varbdd_to_subs(const alt* a, size_t rl, size_t level, cr_spbdd_handle v) const;
	void rule_get_grounds(cr_spbdd_handle& h, size_t rl, size_t level,
		cb_ground f);
	void term_get_grounds(const term& t, size_t level, cb_ground f);
	std::set<witness> get_witnesses(const term& t, size_t l);
	bool get_proof(const term& q, proof& p, size_t level, size_t dep=-1);
	void run_internal_prog(flat_prog p, std::set<term>& r, size_t nsteps=0);
	void print_env(const env& e, const rule& r) const;
	void print_env(const env& e) const;
	template <typename T>
	void out(std::basic_ostream<T>&, spbdd_handle, ntable) const;
	void out(spbdd_handle, ntable, const rt_printer&) const;

	bool handler_eq(const term& t, const varmap &vm, const size_t vl,
			spbdd_handle &c) const;
	bool handler_leq(const term& t, const varmap &vm, const size_t vl,
			spbdd_handle &c) const;

	bool get_facts(const flat_prog& m);
	void get_alt(const term_set& al, const term& h, std::set<alt>& as,
		bool blt = false);
	void get_form(const term_set& al, const term& h, std::set<alt>& as);
	bool get_rules(flat_prog m);

	ntable get_table(const sig& s);
	ntable get_new_tab(int_t x, ints ar);
	lexeme get_new_rel();
	void load_string(lexeme rel, const string_t& s);
	lexeme get_var_lexeme(int_t i);
	bool add_prog_wprod(flat_prog m, const std::vector<struct production>&,
		bool mknums = false);
	bool contradiction_detected();
	bool infloop_detected();
	char fwd() noexcept;
	level get_front() const;

	bool bodies_equiv(std::vector<term> x, std::vector<term> y) const;
	ntable prog_add_rule(flat_prog& p, std::map<ntable, ntable>& r,
		std::vector<term> x);
//	std::map<ntable, std::set<spbdd_handle>> goals;
	std::set<term> goals;
	std::set<ntable> to_drop;
	strs_t strs;
	std::set<int_t> str_rels;
	flat_prog prog_after_fp; // prog to run after a fp (for cleaning nulls)

	//	std::function<int_t(void)>* get_new_rel;

	bool print_updates_check();

	// tml_update population
	int_t rel_tml_update, sym_add, sym_del;
	void init_tml_update();
	void add_tml_update(const term& rt, bool neg);
	template <typename T>
	std::basic_ostream<T>& decompress_update(std::basic_ostream<T>&,
	spbdd_handle& x, const rule& r); // decompress for --print-updates and tml_update

	//-------------------------------------------------------------------------
	//builtins
	builtins bltins;

	bool init_builtins();
	bool init_print_builtins();
	bool init_js_builtins();
	bool init_bdd_builtins();

	// simple builtin execution from a fact
	void fact_builtin(const term& b);

	// called when executing builtin in rule's head
	// @param hs alt_query bdd handles
	// @param tbl builtin's table
	// @param tab id of builtin's table
	void head_builtin(const bdd_handles& hs, const table& tbl, ntable tab);

	// called when executing builtins in body
	// @param x  result of a var grounding query
	// @param a  alt
	// @param hs alt query bdd handles (output is inserted here)
	void body_builtins(spbdd_handle x, alt* a, bdd_handles& hs);

	//-------------------------------------------------------------------------
	//arithmetic/fol support
	void ex_typebits(spbdd_handle &s, size_t nvars) const;
	void ex_typebits(bools &exvec, size_t nvars) const;
	spbdd_handle ex_typebits(size_t in_varid, spbdd_handle in, size_t n_vars);
	void append_num_typebits(spbdd_handle &s, size_t nvars) const;
	spbdd_handle perm_from_to(size_t from, size_t to, spbdd_handle in, size_t n_bits,
		size_t n_vars);
	spbdd_handle perm_bit_reverse(spbdd_handle in,  size_t n_bits, size_t n_vars);
	void set_constants(const term& t, spbdd_handle &q) const;
	void handler_form1(pnft_handle &p, form *f, varmap &vm, varmap &vmh, bool fq);
	void handler_formh(pnft_handle &p, form *f, varmap &vm, varmap &vmh);
	bool handler_arith(const term& t, const varmap &vm, const size_t vl,
		spbdd_handle &cons);
	spbdd_handle add_var_eq(size_t arg0, size_t arg1, size_t arg2, size_t args);
	spbdd_handle full_addder_carry(size_t var0, size_t var1, size_t n_vars,
		uint_t b, spbdd_handle r) const;
	spbdd_handle full_adder(size_t var0, size_t var1, size_t n_vars,
		uint_t b) const;
	spbdd_handle constrain_to_num(size_t var, size_t n_vars) const;
	spbdd_handle shr(size_t var0, size_t n1, size_t var2, size_t n_vars);
	spbdd_handle shl(size_t var0, size_t n1, size_t var2, size_t n_vars);
	spbdd_handle add_ite(size_t var0, size_t var1, size_t args, uint_t b,
		uint_t s);
	spbdd_handle add_ite_carry(size_t var0, size_t var1, size_t args, uint_t b,
		uint_t s);
	spbdd_handle mul_var_eq(size_t var0, size_t var1, size_t var2,
		size_t n_vars);
	spbdd_handle mul_var_eq_ext(size_t var0, size_t var1, size_t var2,
		size_t var3, size_t n_vars);
	spbdd_handle bitwise_handler(size_t in0_varid, size_t in1_varid, size_t out_varid,
		spbdd_handle in0, spbdd_handle in1, size_t n_vars, t_arith_op op);
	spbdd_handle pairwise_handler(size_t in0_varid, size_t in1_varid, size_t out_varid,
		spbdd_handle in0, spbdd_handle in1, size_t n_vars, t_arith_op op);
	t_arith_op get_bwop(lexeme l);
	t_arith_op get_pwop(lexeme l);

	void fol_query(cr_pnft_handle f, bdd_handles& v);
	void hol_query(cr_pnft_handle f, bdd_handles& v, bdd_handles &v2, std::vector<bdd_handles> &hvarmap,
			std::vector<quant_t> &quantsh, varmap &vmh);
	void pr(spbdd_handle& b, spbdd_handle &vh, bdd_handles &vm, bool neg);
	void formula_query(cr_pnft_handle f, bdd_handles& v);


	//-------------------------------------------------------------------------
	//printer
	template <typename T>
	void print(std::basic_ostream<T>&, const proof_elem&);
	template <typename T>
	void print(std::basic_ostream<T>&, const proof&);
	template <typename T>
	void print(std::basic_ostream<T>&, const witness&);
	template <typename T>
	std::basic_ostream<T>& print(std::basic_ostream<T>&,
		const std::set<term>& b) const;
	template <typename T>
	std::basic_ostream<T>& print(std::basic_ostream<T>&, const term& h,
		const std::set<term>& b) const;
	template <typename T>
	std::basic_ostream<T>& print(std::basic_ostream<T>&, const rule& r)
		const;
	template <typename T>
	std::basic_ostream<T>& print(std::basic_ostream<T>&, const sig& s)
		const;
	template <typename T>
	std::basic_ostream<T>& print(std::basic_ostream<T>&, const table& t)
		const;
	template <typename T>
	std::basic_ostream<T>& print(std::basic_ostream<T>&) const;

	template <typename T>
	std::basic_ostream<T>& print(std::basic_ostream<T>&, const std::vector<term>& b)
		const;
	template <typename T>
	std::basic_ostream<T>& print(std::basic_ostream<T>&, const flat_prog& p)
		const;
	template <typename T>
	std::basic_ostream<T>& print_dict(std::basic_ostream<T>&) const;

public:

	rt_options opts;
	environment typenv;
	ir_builder *ir_handler;

	tables(dict_t& dict, rt_options opts, ir_builder *ir_handler);
	~tables();
	size_t step() { return nstep; }
	bool add_prog(const raw_prog& p, const strs_t& strs);

	static bool run_prog(const raw_prog &rp, dict_t &dict, const options &opts,
		std::set<raw_term> &results);
	static bool run_prog_wedb(const std::set<raw_term> &edb, raw_prog rp,
		dict_t &dict, const options &opts, std::set<raw_term> &results);
	bool run_prog_wstrs(const raw_prog& p, const strs_t& strs, size_t steps = 0,
		size_t break_on_step = 0);

	bool run_nums(flat_prog m, std::set<term>& r, size_t nsteps);
	bool pfp(size_t nsteps = 0, size_t break_on_step = 0);
	template <typename T>
	void out(std::basic_ostream<T>&) const;
	template <typename T>
	bool out_fixpoint(std::basic_ostream<T>& os);
	void out(const rt_printer&) const;
#ifdef __EMSCRIPTEN__
	void out(emscripten::val o) const;
#endif
	void set_proof(bool v) { opts.bproof = v; }
	template <typename T>
	bool get_goals(std::basic_ostream<T>&);
	dict_t& get_dict() { return dict; }

	// adds __fp__() fact into the db when FP found (enabled by -fp or -g)
	bool add_fixed_point_fact();

	// transform nested programs into a single program controlled by guards
	void transform_guards(raw_prog& rp);
	// recursive fn for transformation of a program and its nested programs
	void transform_guards_program(raw_prog& target_rp, raw_prog& rp,
		int_t& prev_id);
	void transform_guard_statements(raw_prog& target_rp, raw_prog& rp);

	// helper functions for creating internal ids = __lx__id1__id2__
	void iid(std::vector<raw_term>& rts, const std::string& lx, int_t i,
		bool neg = false);
	void iid(std::vector<raw_term>& rts, const std::string& lx, int_t i,
		int_t i2, bool neg = false);
	void iid(std::vector<raw_term>& rts, const lexeme& lx, bool neg=0);
	lexeme lx_id(std::string name, int_t id = -1, int_t id2 = -1);

	void add_print_updates_states(const std::set<std::string> &tlist);
	bool populate_tml_update = false;
	bool print_updates       = false;
	bool print_steps         = false;
	bool error               = false;

};


#ifdef WITH_EXCEPTIONS
struct unsat_exception : public std::exception {
	virtual const char* what() const noexcept { return "unsat."; }
};

struct contradiction_exception : public unsat_exception {
	virtual const char* what() const noexcept {
		return err_contradiction;
	}
};

struct infloop_exception : public unsat_exception {
	virtual const char* what() const noexcept {
		return err_infloop;
	}
};
#endif

//#endif
