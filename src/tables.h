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

#ifndef __TABLES_H__
#define __TABLES_H__

#include <map>
#include <vector>
#include <tuple>
#include <functional>
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

// TODO remove include and add alternative ones
//#ifndef REMOVE_IR_BUILDER_FROM_TABLES
#include "ir_builder.h"
//#else
//typedef std::set<std::vector<term>> flat_prog;
//#endif // REMOVE_IR_BUILDER_FROM_TABLES

class tables;

struct body {
	bool neg = false;
	ntable tab;
	bools ex;
	uints perm;
	spbdd_handle q, tlast, rlast;
	bool operator<(const body& t) const {
		if (q != t.q) return q < t.q;
		if (neg != t.neg) return neg;
		if (tab != t.tab) return tab < t.tab;
		if (ex != t.ex) return ex < t.ex;
		return perm < t.perm;
	}
};

struct alt : public std::vector<body*> {
	spbdd_handle rng = htrue, eq = htrue;
	size_t varslen = 0;
	// The last solutions of this alternative's constituent body terms
	bdd_handles last;
	// The conjunction of last, eq, and range. Only used when proofs enabled.
	spbdd_handle unquantified_last = hfalse;
	// unquantified_last with variables existentially quantified (ex) and permuted
	// (perm)
	spbdd_handle rlast = hfalse;
	std::vector<term> t;
	std::vector<term> bltins; // builtins to run during alt_query
	bools ex;
	uints perm;
	varmap vm;
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

//#ifdef PROOF
struct gnode {
	enum gntype{
		pack, interm, symbol
	} type;
	const term &t;
	int lev;
	std::vector<gnode*> next;
	gnode(int level, const term &_t, gntype typ = symbol ): t(_t),lev(level) {
		type = typ; }
	gnode(int level, const term &_t, std::vector<gnode*> inter): t(_t),lev(level){
		type = interm;
		this->next.emplace_back(new gnode(lev, t, gnode::gntype::pack));
		next.back()->next = inter;
	}
	bool binarise() {
		interm2g.clear();
		visited.clear();
		return _binarise();
	}
	private:
	static std::set<const gnode*> visited;
	static std::map<std::set<term>, gnode*> interm2g;
	bool _binarise();
};
//#endif

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
	bool commit(DBG(size_t));
	inline bool is_builtin() const { return idbltin > -1; }
};

#ifdef REMOVE_IR_BUILDER_FROM_TABLES
class progress {
public:
	progress() {};
	virtual ~progress() = default;
	virtual void notify_update(tables &ts, spbdd_handle& x, const rule& r) = 0;
};
#endif // REMOVE_IR_BUILDER_FROM_TABLES

class tables {
	friend std::ostream& operator<<(std::ostream& os, const tables& tbl);
	friend std::istream& operator>>(std::istream& is, tables& tbl);
	friend struct form;
	friend struct pnft;
	friend struct term;
	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
	friend class ir_builder;
	#endif // REMOVE_IR_BUILDER_FROM_TABLES
	friend class driver;
	friend struct bit_univ;
	friend struct progress;

private:

	typedef std::function<void(size_t,size_t,size_t, const std::vector<term>&)>
		cb_ground;
	typedef std::function<void(const term&)> cb_decompress;

	std::set<body*, ptrcmp<body>> bodies;
	std::set<alt*, ptrcmp<alt>> alts;

public:

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

	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
	typedef std::function<void(const raw_term&)> rt_printer;
	#endif

	nlevel nstep = 0;

	std::vector<table> tbls;
private:
	std::vector<rule> rules;
	std::vector<bdd_handles> fronts;
	std::vector<bdd_handles> levels;

	void get_sym(int_t s, size_t arg, size_t args, spbdd_handle& r) const;
	void get_var_ex(size_t arg, size_t args, bools& b) const;
	void get_alt_ex(alt& a, const term& h) const;

	#ifdef TYPE_RESOLUTION
	size_t bits = 0;
	#else
	size_t bits = 2;
	#endif

	#ifndef REMOVE_DICT_FROM_TABLES
	dict_t& dict;
	#endif // REMOVE_DICT_FROM_TABLES

	bool datalog, halt = false, unsat = false, bcqc = false;

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
	std::pair<std::vector<size_t>, std::vector<size_t>> _inverse(
			size_t bits,
			size_t args) const {
		std::vector<size_t> _args(bits * args);
		std::vector<size_t> _bits(bits * args);
		for (size_t arg = 0; arg < args; ++arg)
			for (size_t bit = 0; bit < bits; ++bit)
				_args[pos(bit, arg, args)] = arg,
				_bits[pos(bit, arg, args)] = bit;
		std::pair<std::vector<size_t>, std::vector<size_t>> i(_bits, _args);
		return i;
	}
	size_t _args(const term* t) const {
		return t->size();
	}
	size_t bit(size_t v, const term* t, const std::vector<size_t>& _bits,
			const std::vector<size_t>& _args) const {
		size_t b = _bits[v];
		size_t i = _args[v];
		return t->at(i) & (1 << b);
	}
	size_t max_pos(const term* t) const {
		return _args(t) * bits -1;
	}

	spbdd_handle from_bit(size_t b, size_t arg, size_t args, int_t n) const {
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
	uints get_perm(const term& t, const varmap& m, size_t len) const;
	template<typename T>
	static varmap get_varmap(const term& h, const T& b, size_t &len,
		bool blt = false);

	spbdd_handle from_term(const term&, body *b = 0,
		std::map<int_t, size_t>*m = 0, size_t hvars = 0);
	body get_body(const term& t, const varmap&, size_t len) const;

	std::pair<bools, uints> deltail(size_t len1, size_t len2) const;
	uints addtail(size_t len1, size_t len2) const;
	spbdd_handle addtail(cr_spbdd_handle x, size_t len1, size_t len2) const;
	spbdd_handle body_query(body& b, size_t);
	spbdd_handle alt_query(alt& a, size_t);

//#ifdef PROOF
	DBG(vbools allsat(spbdd_handle x, size_t args) const;)
public:
	void decompress(spbdd_handle x, ntable tab, const cb_decompress&,
		size_t len = 0, bool allowbltins = false) const;
	spbdd_handle from_fact(const term& t);
	std::set<term> decompress();
private:
	rule new_identity_rule(ntable tab, bool neg);
	bool is_term_valid(const term &t);
	bool get_dnf_proofs(const term& q, proof& p, size_t level,
		std::set<std::pair<term, size_t>> &refuted, size_t explicit_rule_count);
	bool get_proof(const term& q, proof& p, size_t level,
		std::set<std::pair<term, size_t>> &refuted, size_t explicit_rule_count);
	void print_dot(std::wstringstream &ss, gnode &gh, std::set<gnode*> &visit, int level = 0);
	bool build_graph( std::map<term, gnode*> &tg, proof &p, gnode &g);
	gnode* get_forest(const term& t, proof& p );
	void print_env(const env& e, const rule& r) const;
	void print_env(const env& e) const;
//#endif

	bool handler_eq(const term& t, const varmap &vm, const size_t vl,
			spbdd_handle &c) const;
	bool handler_leq(const term& t, const varmap &vm, const size_t vl,
			spbdd_handle &c) const;
	void handler_bitunv(std::set<std::pair<body,term>>& b, const term& t, alt& a);

	bool get_facts(const flat_prog& m) ;
	bool is_optimizable_fact(const term& t) const;
	std::map<ntable, spbdd_handle> from_facts(
		std::map<ntable, std::vector<const term*>>& pending,
		const std::map<ntable, std::pair<std::vector<size_t>, std::vector<size_t>>> &inverses) const;
	spbdd_handle from_facts(std::vector<const term*>& pending,
		const std::pair<std::vector<size_t>, std::vector<size_t>>& inverse) const;
	spbdd_handle from_facts(std::vector<const term*>& terms,
		std::vector<const term*>::iterator left,
		std::vector<const term*>::iterator right,
		const size_t& pos,
		const std::pair<std::vector<size_t>, std::vector<size_t>>& inverse) const;
	spbdd_handle from_bit(const std::vector<const term*>::iterator& current,
		const std::pair<std::vector<size_t>, std::vector<size_t>>& inverse) const;

	void get_alt(const term_set& al, const term& h, std::set<alt>& as,
		bool blt = false);
	bool get_rules(flat_prog& m);

	//lexeme get_var_lexeme(int_t i);
	bool add_prog_wprod(flat_prog m, const std::vector<struct production>&);
	bool contradiction_detected();
	bool infloop_detected();

	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
	char fwd() noexcept;
	#else 
	char fwd(progress& p) noexcept;
	#endif // REMOVE_IR_BUILDER_FROM_TABLES

	bdd_handles get_front() const;
	bool bodies_equiv(std::vector<term> x, std::vector<term> y) const;
	std::set<term> goals;
	std::set<ntable> to_drop;
#ifndef LOAD_STRS
	void load_string(lexeme rel, const string_t& s);
	strs_t strs;
	std::set<int_t> str_rels;
#endif
public:
	flat_prog prog_after_fp; // prog to run after a fp (for cleaning nulls)

#ifndef REMOVE_UPDATES_FROM_TABLE
	// tml_update population
	int_t rel_tml_update, sym_add, sym_del;
#endif // #ifdef REMOVE_UPDATES_FROM_TABLE

private:
	#ifndef REMOVE_UPDATES_FROM_TABLE
	void init_tml_update();
	#endif // REMOVE_UPDATES_FROM_TABLE

	bool print_updates_check();

	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
	void add_tml_update(const term& rt, bool neg);
	template <typename T>
	std::basic_ostream<T>& decompress_update(std::basic_ostream<T>&,
		spbdd_handle& x, const rule& r); // decompress for --print-updates and tml_update
	#endif // REMOVE_IR_BUILDER_FROM_TABLES


	//-------------------------------------------------------------------------
	//builtins
	
	#ifndef REMOVE_DICT_FROM_BUILTINS
	
	bool init_builtins();
	bool init_print_builtins();
	bool init_js_builtins();
	bool init_bdd_builtins();
	#endif // REMOVE_DICT_FROM_BUILTINS

	#ifdef REMOVE_UPDATES_FROM_TABLE
	updates updts;
	#endif // REMOVE_UPDATES_FROM_TABLE

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
	spbdd_handle ex_typebits(size_t in_varid, spbdd_handle in, size_t n_vars);
	void append_num_typebits(spbdd_handle &s, size_t nvars) const;
	spbdd_handle perm_from_to(size_t from, size_t to, spbdd_handle in, size_t n_bits,
		size_t n_vars);
	spbdd_handle perm_bit_reverse(spbdd_handle in,  size_t n_bits, size_t n_vars);
	spbdd_handle perm_bit_reverse_bt(spbdd_handle in, size_t n_bits, size_t delta);
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

	#ifdef FOL_V1
	std::pair<bools, uints> deltail(size_t len1, size_t len2, size_t bits) const;
	void ex_typebits(spbdd_handle &s, size_t nvars) const;
	void ex_typebits(bools &exvec, size_t nvars) const;
	uints get_perm(const term& t, const varmap& m, size_t len, size_t bits) const;
	void get_form(const term_set& al, const term& h, std::set<alt>& as);
	void fol_query(cr_pnft_handle f, bdd_handles& v);
	void hol_query(cr_pnft_handle f, std::vector<quant_t> &quantsh, var2space &v2s, bdd_handles &v);
	void formula_query(cr_pnft_handle f, bdd_handles& v);
	#endif

	//-------------------------------------------------------------------------
	//printer
	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
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

	#endif // REMOVE_IR_BUILDER_FROM_TABLES

	#ifndef REMOVE_DICT_FROM_TABLES
	template <typename T>
	std::basic_ostream<T>& print_dict(std::basic_ostream<T>&) const;
	#endif // REMOVE_DICT_FROM_TABLES
public:

	struct output {

		void term(term &t);
	};

	rt_options opts;
	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
	ir_builder *ir_handler;
	#endif // REMOVE_IR_BUILDER_FROM_TABLES
	builtins bltins;

	#ifdef REMOVE_DICT_FROM_BUILTINS
	tables(rt_options opts, builtins &bltins);
	#else
	tables(dict_t& dict, rt_options opts, ir_builder *ir_handler);
	#endif // REMOVE_DICT_FROM_BUILTINS
	
	~tables();
	
	size_t step() { return nstep; }
	
	bool add_prog_wprod(const raw_prog& p, const strs_t& strs);

	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
	static bool run_prog_wedb(const std::set<raw_term> &edb, raw_prog rp,
		dict_t &dict, const options &opts, std::set<raw_term> &results);
	bool run_prog(const raw_prog& p, const strs_t& strs, size_t steps = 0,
		size_t break_on_step = 0);
	bool pfp(size_t nsteps = 0, size_t break_on_step = 0);
	#else 
	static bool run_prog_wedb(const std::set<raw_term> &edb, raw_prog rp,
		dict_t &dict, builtins& bltins, const options &opts, std::set<raw_term> &results,
		progress& p);
	bool run_prog(const raw_prog& p, const strs_t& strs, size_t steps,
		size_t break_on_step, progress& ps);
	bool pfp(size_t nsteps, size_t break_on_step, progress& p);
	#endif // REMOVE_IR_BUILDER_FROM_TABLES

	bool compute_fixpoint(bdd_handles &trues, bdd_handles &falses, bdd_handles &undefineds);
	bool is_infloop();
	
	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
	template <typename T> void out(std::basic_ostream<T>&) const;
	template <typename T> bool out_fixpoint(std::basic_ostream<T>& os);
	template <typename T> bool out_goals(std::basic_ostream<T>&);
	void out(const rt_printer&) const;
	void out(spbdd_handle, ntable, const rt_printer&) const;
	template <typename T>
	void out(std::basic_ostream<T>&, spbdd_handle, ntable) const;
	template <typename T>bool get_proof(std::basic_ostream<T>& os);
	#endif

	void set_proof(proof_mode v) { opts.bproof = v; }
	
	#ifndef REMOVE_DICT_FROM_TABLES
	dict_t& get_dict() { return dict; }
	#endif // REMOVE_DICT_FROM_TABLES

#ifdef __EMSCRIPTEN__
	void out(emscripten::val o) const;
#endif

	// adds __fp__() fact into the db when FP found (enabled by -fp or -g)
	bool add_fixed_point_fact();
	#ifndef REMOVE_ADD_PRINT_UPDATE_STATES_FROM_TABLES
	void add_print_updates_states(const std::set<std::string> &tlist);
	#endif // REMOVE_ADD_PRINT_UPDATE_STATES_FROM_TABLES
	
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

#endif // __TABLES_H__