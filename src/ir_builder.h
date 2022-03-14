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

#ifndef _IR_BUILDER_H_
#define _IR_BUILDER_H_

#include "err.h"
#include "defs.h"
#include "term.h"
#include "analysis.h"

typedef std::set<std::vector<term>> flat_prog;
typedef std::pair<int_t, ints> sig;

class tables;

class ir_builder {

private:

public:

	int_t syms = 0, nums = 0, chars = 0;
	dict_t &dict;
	rt_options opts;
	//environment &typenv;
	tables *dynenv = 0;
	tables *printer = 0;

	int  regex_level = 0;
	bool error = false;

	ir_builder(dict_t& dict_, rt_options& opts_/*, environment& env_*/);
	~ir_builder();

	flat_prog to_terms(const raw_prog& p);
	term from_raw_term(const raw_term&, bool ishdr = false, size_t orderid = 0);
	bool from_raw_form(const sprawformtree rs, form *&froot, bool &is_sol);
	raw_term to_raw_term(const term& t) const;

	struct elem get_elem(int_t arg) const;
	void get_nums(const raw_term& t);

	sig get_sig(const term& t);
	sig get_sig(const raw_term& t);
	sig get_sig(const lexeme& rel, const ints& arity);
	size_t sig_len(const sig& s);

	bool to_pnf( form *&froot);

	int_t get_factor(raw_term &rt, size_t &n, std::map<size_t, term> &ref,
					std::vector<term> &v, std::set<term> &done);
	bool get_rule_substr_equality(std::vector<std::vector<term>> &eqr);
	bool get_substr_equality(const raw_term &rt, size_t &n, std::map<size_t, term> &ref,
					std::vector<term> &v, std::set<term> &done);

	bool transform_grammar(std::vector<struct production> g, flat_prog& p, form *&root);
	bool transform_ebnf(std::vector<struct production> &g, dict_t &d, bool &changed);
	bool transform_grammar_constraints(const struct production &x, std::vector<term> &v,
			flat_prog &p,std::map<size_t, term> &refs);

	template <typename T>
	bool er(const T& data) { return error=true, throw_runtime_error(data); }

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
};

struct unary_string{
	//IMPROVE: use array [ pos] = rel or unorderedmap instead
	std::unordered_map< char32_t, std::set<int_t> > rel;
	size_t pbsz;
	uint64_t vmask;
	std::vector<char32_t> sort_rel;

	unary_string(size_t _pbsz);
	bool buildfrom(string_t s) { return buildfrom(to_u32string(s)); }
	bool buildfrom(std::u32string s);
	string_t getrelin_str(char32_t r);
	ostream_t& toprint(ostream_t& o);
};

struct transformer;

//TODO: ? define a container with type of formula as
//struct formula { form* root,  type: FOL/SOL/ARITH/CONSTRAINT};
struct form {
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

	//evaluation of is_sol,
	//alternatively from_raw_terms gets it as well by using a new argument
	bool is_sol();
	bool implic_rmoval();

	~form() {
		if(l) delete l, l = NULL;
		if(r) delete r, r = NULL;
		if(tm) delete tm, tm = NULL;
	}
	void printnode(int lv=0, const ir_builder* tb = NULL);
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

struct ptransformer{
	struct production &p;
	std::vector<struct production> lp;
	dict_t &d;

	ptransformer(struct production &_p, dict_t &_d ): p(_p), d(_d) { }
	bool parse_alt( std::vector<elem> &next, size_t& cur);
	bool is_firstoffactor(elem &c);
	bool parse_alts( std::vector<elem> &next, size_t& cur);
	lexeme get_fresh_nonterminal();
	bool synth_recur( std::vector<elem>::const_iterator from,
		std::vector<elem>::const_iterator till, bool bnull, bool brecur,
		bool balt);
	bool parse_factor( std::vector<elem> &next, size_t& cur);
	bool visit( );
};

struct graphgrammar {
	enum mark {
		NONE,
		PROGRESS,
		VISITED
	};
	dict_t &dict;
	std::vector<elem> sort;
	std::multimap<elem, std::pair<production, mark> > _g;
	typedef std::multimap<elem, std::pair<production, mark> >::iterator _itg_t;
	graphgrammar(std::vector<production> &t, dict_t &_d);
	bool dfs( const elem &s);
	bool detectcycle();
	bool iscyclic( const elem &s);
	std::string get_regularexpstr(const elem &p, bool &bhasnull, bool islazy);
	const std::map<lexeme, std::string, lexcmp> & get_builtin_reg();
	bool combine_rhs( const elem &s, std::vector<elem> &comb);
	bool collapsewith();
};

#endif
