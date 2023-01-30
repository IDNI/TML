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
#include "typemanager.h"
//#include "../lib/parser/src/parser.h"

namespace idni {

typedef std::set<std::vector<term>> flat_prog;
//typedef idni::parser<char32_t> parser_t;

#ifdef TYPE_RESOLUTION
struct rt_vartypes {
	int_t rt_idx = 0;
	ints positions;
	tml_natives types;
	bool operator==(const int_t& idx) const {
		return (rt_idx == idx);
	}
	rt_vartypes(const int_t &idx_) : rt_idx(idx_) { };
	rt_vartypes(const int_t &idx_, const ints &pos_) : rt_idx(idx_), positions(pos_) { };
	void append(const tml_native_t &t);
};

typedef std::map<int_t, std::vector<rt_vartypes>> rr_varmap;
#endif

#ifdef BIT_TRANSFORM
struct table;
#endif
class tables;

typedef std::set<term> clause;
typedef std::set<clause> dnf;
typedef std::vector<std::pair<term, dnf>> prog;

class ir_builder {

public:
	int_t syms = 0, nums = 0, chars = 0;
	dict_t &dict;
	rt_options opts;
	tables *dynenv = 0;
	tables *printer = 0;
	int  regex_level = 0;
	bool error = false;

	std::map<sig, int_t> tsmap; //signature-table_id map
	std::map<sig, int_t> bsmap; //signature-bltin_id map

	ir_builder(dict_t& dict_, rt_options& opts_):
		dict(dict_), opts(opts_) {} 

	~ir_builder() = default;

	//-------------------------------------------------------------------------

#ifdef TYPE_RESOLUTION
	std::map<int_t, std::vector<tml_natives>> relid_argtypes_map;
	bool append(std::map<int_t, std::vector<tml_natives>> &m, sig &s);
	void set_vartypes(int_t i, ints &mp, rr_varmap &v, raw_rule &auxr);
	rr_varmap get_vars(raw_rule &r);
	void get_vars_rel(const raw_term& t, int_t idx, rr_varmap& v);
	void get_vars_eq(const raw_term& t, int_t idx, rr_varmap& v);
	void get_vars_leq(const raw_term& t, int_t idx, rr_varmap& v);
	void get_vars_arith(const raw_term& t, int_t idx, rr_varmap& v);
	void get_vars_bltin(const raw_term&t, int_t idx, rr_varmap& v);

	raw_prog generate_type_resolutor(raw_prog &rp);
	void type_resolve_facts(std::vector<raw_rule> &rp);
	void type_resolve_bodies(raw_rule &r, rr_varmap &v);
	bool type_resolve_rules(std::vector<raw_rule> &rp);
	void type_resolve(raw_prog &rp);

	sig get_sig_bltin(raw_term&t);
	sig get_sig_eq(const raw_term&t);
	sig get_sig_arith(const raw_term&t);
	sig get_sig_typed(const lexeme& rel, std::vector<native_type> tys);
	sig get_sig_typed(const int& rel_id, std::vector<native_type> tys);
	sig to_native_sig(const term& e);

	int_t get_bltin(const sig& s);

	#ifdef BIT_TRANSFORM_V2
	void bit_transform(tml_natives &ts, tml_natives &rts, ints &t, ints &bt);
	void bit_transform_inv(tml_natives &ts, const ints &tb, ints &t);
	#endif
	void natives2raw(int_t args, const ints &r, const sig &s, raw_term &rt);
#endif

	sig get_sig(raw_term& t);
	sig get_sig(const raw_term& t);
	sig get_sig(const lexeme& rel, const ints& arity);
	sig get_sig(const int_t& rel_id, const ints& arity);
	size_t sig_len(const sig& s) const;

	std::set<int_t> str_rels;
#define LOAD_STRS
#ifdef LOAD_STRS
	strs_t strs;
	void load_string(flat_prog &fp, const lexeme &r, const string_t& s);
	void load_strings_as_fp(flat_prog &fp, const strs_t& s);
#endif

	//-------------------------------------------------------------------------
	flat_prog to_terms(const raw_prog& p);
	term from_raw_term(const raw_term&, bool ishdr = false, size_t orderid = 0);
	raw_term to_raw_term(const term& t);
	int_t get_table(const sig& s);
	struct elem get_elem(int_t arg) const;
	void get_nums(const raw_term& t);
	void set_hidden_table(const int_t t);
	
	//-------------------------------------------------------------------------
	bool to_pnf(form *&froot);
	#ifdef FOL_V1
	bool from_raw_form(const sprawformtree rs, form *&froot, bool &is_sol);
	#endif
	#ifdef FOL_V2
	prog get_fof(sprawformtree root);
	#endif

	int_t get_factor(raw_term &rt, size_t &n, std::map<size_t, term> &ref,
					std::vector<term> &v, std::set<term> &done);
	bool get_rule_substr_equality(std::vector<std::vector<term>> &eqr);
	bool get_substr_equality(const raw_term &rt, size_t &n, std::map<size_t, term> &ref,
					std::vector<term> &v, std::set<term> &done);

//	parser_t::grammar to_grammar(const std::vector<struct production> &g)
//		const;
//	void add_parsed_facts(flat_prog& p, const parser_t& pr);

	bool transform_grammar(std::vector<struct production> g, flat_prog& p);
	bool transform_apply_regex(std::vector<struct production> &g,  flat_prog& p);
	bool transform_alts( std::vector<struct production> &g);
	bool transform_strsplit(std::vector<struct production> &g);
	bool transform_ebnf(std::vector<struct production> &g, dict_t &d, bool &changed);
	bool transform_grammar_constraints(const struct production &x, std::vector<term> &v,
			flat_prog &p,std::map<size_t, term> &refs);
	template <typename T>
	bool er(const T& data) { return error=true, throw_runtime_error(data); }

	//-------------------------------------------------------------------------
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

	//-------------------------------------------------------------------------
	// bit universe
#ifdef BIT_TRANSFORM
	typemanager tc;
	void bit_transform(raw_prog &rp, size_t bo) {
		if(tc.type_check(rp)) {
			set_pos_func(bo);
			btransform(rp);
		}
	}
	bool bitunv_to_raw_term(raw_term &rt) {
		return brev_transform(rt);
	}
	bool bitunv_decompress(const term &t, const table &tb) {
		return brev_transform_check(t,tb);
	}

	size_t bit_order = 0;

	enum { //should be compatible with typesystem's prim type
		CHAR_BSZ = 8,
		INT_BSZ = 8,
		SYM_BSZ = 8,
		VAR_BSZ = 8,
	};
    inline static primtype dt_nop;
	inline static primtype dt_int= primtype(primtype::UINT);

	size_t char_bsz = CHAR_BSZ, int_bsz = INT_BSZ, sym_bsz = SYM_BSZ;
	size_t var_bsz = VAR_BSZ;

	typedef std::vector<size_t> tab_args;
	typedef std::function< size_t ( size_t , size_t , size_t , size_t, tab_args) > posfunc;
	posfunc pos;

	void set_pos_func(size_t bo_) {
		bit_order = bo_;
		this->pos = [this](size_t a, size_t b, size_t c, size_t d, tab_args t)-> size_t {
				return this->pos_gen(a, b, c, d, t); };
	}

	std::vector<primtype> get_arg_types( const raw_term & rt, const raw_rule & rr);
	void append_types(string_t &, std::vector<primtype>&) ;
	const primtype& get_typeinfo(size_t n, const raw_term& rt, const raw_rule &rr );
	size_t pos_eqsz(size_t bsz, size_t bit_from_right , size_t arg, size_t args /*,tab_args rtab */ ) {
		DBG(assert(bit_from_right < bsz && arg < args); )
		return (bsz - bit_from_right - 1)* args + arg;
	}
	size_t pos_gen(size_t
	#ifdef DEBUG
	bsz
	#endif
	, size_t bit_from_right , size_t arg, size_t args, tab_args rtab  ) {
		DBG(assert(bit_from_right < bsz && arg < args); )
		size_t pos = -1;
		size_t max_bits=0;
		for (size_t bits : rtab) max_bits = std::max(max_bits, bits);
		for (size_t bit = 0; bit < max_bits; bit++)
			for (size_t a= 0 ; a<args ; a++) {
				if (bit < rtab[a]) pos++;
				if (bit == bit_from_right && arg == a) goto end;
			}
		end: return pos;
	}

	size_t pos_neqsz(size_t bsz, size_t bit_from_right , size_t arg, size_t args, tab_args rtab  ) {
		DBG(assert(bit_from_right < bsz && arg < args && args == rtab.size() && rtab[arg] == bsz); )
		DBG(COUT<< arg << " "<<  args << " "<<  bit_from_right << " "<< (bsz - bit_from_right -1) << " " <<bsz << " " );
		bools szsort(64); //max number of args <=64 in radix sorted form
		size_t skip = 0, cargs  = 0; // # of args with sz less than bit_rom_right;
		for (size_t i = 0 ; i <rtab.size(); i++) {
			szsort[rtab[i]] = true;
			if( (bsz -bit_from_right -1) < rtab[i]  ) cargs++;
			else if( i <= arg ) skip++;  //to adjust arg to be within carg range
		}
		size_t lastsz=0, base=0,  s = args;
		for( size_t sz = 0; sz < szsort.size() && sz <= (bsz - bit_from_right -1) ; sz++)
			if(szsort[sz]) {
				base = ((sz-lastsz) * s-- ) + base, lastsz = sz; }
		return base + (bsz - bit_from_right - 1 - lastsz)*cargs + (arg -skip);
    }
	size_t pos_default(size_t bsz, size_t bit_from_right , size_t
	#ifdef DEBUG
	arg
	#endif
	, size_t
	#ifdef DEBUG
	args
	#endif
/*, tab_args rtab */ ) {
		DBG(assert(bit_from_right < bsz && arg < args); )
		return (bsz - bit_from_right - 1); //* args + arg;
	}

	bool brev_transform(raw_term& bit_raw_term);
	bool brev_transform_check(const struct term &t, const struct table &tab);
	bool btransform(raw_prog& rpin);
private:
	bool btransform(const raw_rule& rrin, raw_rule &rrout );
	bool btransform(const raw_term& rtin, raw_term &rtout, const raw_rule &rr, raw_rule &rrout);
	bool btransform(const raw_form_tree& rfin, raw_form_tree &rfout, const raw_rule& rrin, raw_rule &rrout);

public:
	template<class T>
	bool permuteorder(std::vector<T> &cont, size_t n, bool backward = false) {
		static std::vector<int_t> ord, rord;
		if (!n) return false;
		std::vector<T> ocont = cont;
		if(ord.size() != cont.size()) {
			// should do more memoization,
			ord.resize(cont.size());
			rord.resize(cont.size());
			for (size_t i=0; i < ord.size(); i++)	ord[i] = i;
			while (n--  &&  std::next_permutation(ord.begin(), ord.end()));
			for (size_t i=0; i<rord.size(); i++)	rord[ord[i]] = i;
			DBG(COUT<<std::endl);
			DBG(for(int_t v: ord) { COUT<< v; })
		}
		// copy values from old array to cont
		DBG(COUT<< std::endl<<"B:"; std::for_each(cont.begin(), cont.end(), [](T val) { COUT<< val; } );)
		for(size_t i=0; i<cont.size(); i++)	cont[i] = ocont[!backward ? ord[i]: rord[i]];
		DBG(COUT<< std::endl<<"A:"; std::for_each(cont.begin(), cont.end(), [](T val) { COUT<< val; } );)
		return true;
	}

#endif
};

//-----------------------------------------------------------------------------

struct unary_string{
	//TODO  : use array [ pos] = rel or unorderedmap instead
	std::unordered_map< char32_t, std::set<int_t> > rel;
	size_t pbsz;
	uint64_t vmask;
	std::vector<char32_t> sort_rel;

	unary_string(size_t _pbsz);
	bool buildfrom(string_t s) { return buildfrom(idni::to_u32string(s)); }
	bool buildfrom(std::u32string s);
	string_t getrelin_str(char32_t r);
	ostream_t& toprint(ostream_t& o);
};

struct transformer;

//TODO: ? define a container with type of formula as
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
	void printnode(int lv=0, ir_builder* tb = 0);
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

struct ptransformer {
	production &p;
	std::vector<production> lp;
	dict_t &d;
	ptransformer(production &_p, dict_t &_d): p(_p), d(_d) {}

	bool parse_alt(std::vector<elem> &next, size_t& cur);
	bool is_firstoffactor(elem &c);
	bool parse_alts(std::vector<elem> &next, size_t& cur);
	lexeme get_fresh_nonterminal();
	bool synth_recur(std::vector<elem>::const_iterator from,
		std::vector<elem>::const_iterator till, bool bnull, bool brecur,
		bool balt);
	bool parse_factor(std::vector<elem> &next, size_t& cur);
	bool visit();
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

string_t unquote(string_t str);

} // idni namespace
#endif
