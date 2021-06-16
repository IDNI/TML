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

#ifndef _ANALYSIS_H_
#define _ANALYSIS_H_
#include "input.h"

struct context {
    std::map<string_t, primtype> context_prim_var;
    std::map<string_t, string_t> context_typedef_var;
    bool operator==(const context& r) const {
        return context_prim_var == r.context_prim_var && context_typedef_var == r.context_typedef_var;
    }
    bool operator!=(const context& r) const {
        return !(*this == r);
    }
    primtype& lookup_prim_var( string_t &var ){
        DBG(assert(context_prim_var.count(var)));
        return context_prim_var[var];
    }
    string_t lookup_typedef_var( string_t &var ){
        DBG(assert( context_typedef_var.count(var)));
        return context_typedef_var[var];
    }
    bool contains_prim_var(string_t &var) const {
        return context_prim_var.find(var) != context_prim_var.end();
    }
    bool contains_typedef_var(string_t &var) const {
        return context_typedef_var.find(var) != context_typedef_var.end() ;
    }

    std::string to_print() const {
        std::string ret;
        ret.append("\n");
        for(auto &it: context_prim_var) 
          ret.append( to_string(it.first)+ ":" + it.second.to_print());
        for(auto &it: context_typedef_var)
          ret.append(to_string(it.first) + ":" + to_string(it.second));
        return ret;
    }
};

class environment {    
    //type signatures for relations/predicates and user defined
    //complex structures if any 
    std::map<string_t, std::vector<typedecl> > predtype;
    std::map<string_t, structype> usertypedef;
    //contexts for vars
    context ctx;
    public:
    bool contains_pred(string_t &key) const{
        return predtype.find(key) != predtype.end(); 
    }
    bool contains_typedef(string_t &key) const{
        return usertypedef.find(key) != usertypedef.end() ; 
    }
    bool contains_prim_var(string_t &var) const {
        return ctx.context_prim_var.find(var) != ctx.context_prim_var.end();
    }
    bool contains_typedef_var(string_t &var) const {
        return ctx.context_typedef_var.find(var) != ctx.context_typedef_var.end() ;
    }
    bool is_init(){
        return predtype.size()>0;
    }
    std::string to_print() const{ 
        std::string ret;
        for( auto &it : predtype){
            ret.append(to_string(it.first) + " (");
            for( auto &s: it.second)
                ret.append(s.to_print()+", ");
            ret.append(")\n");    
        }
        return ret;
    }
    bool build_from( const raw_term &rt, bool infer);
    bool build_from( const raw_rule &rr);
    bool build_from( const raw_prog &rp  );
    bool build_from( const std::vector<struct typestmt> & );
    const std::vector<typedecl>& lookup_pred( const string_t k  )  const {
        return predtype.find(k)->second;
    }
    structype& lookup_typedef( string_t &k  ) {
        return usertypedef[k];
    }
    bool addtocontext(string_t &var, const primtype &pt ) {
        ctx.context_prim_var[var] = pt;
        return true;
    }
    bool addtocontext(string_t &var, const structype &st ) {
        ctx.context_typedef_var[var] = lexeme2str(st.structname.e);
        return true;
    }
    bool addtocontext(string_t &var, const string_t &stname ) {
        ctx.context_typedef_var[var] = stname;
        return true;
    }
    context& get_context(){
        return ctx;
    }
    void resetAll(){
        reset_context();
        predtype.clear();
        usertypedef.clear();
    }
    void reset_context(){
        ctx.context_prim_var.clear();
        ctx.context_typedef_var.clear();
    }
    primtype& lookup_prim_var( string_t &var ){
        DBG(assert(ctx.context_prim_var.count(var)));
           return ctx.context_prim_var[var];
    }
    structype& lookup_typedef_var( string_t &var ){
        DBG(assert( ctx.context_typedef_var.count(var)));
        return usertypedef[ctx.lookup_typedef_var(var)];
    }
};
class typechecker { 
    public:
    typechecker(raw_prog &p, bool _infer = false) : rp(p),infer(_infer), env(p.get_typenv()) {
        env.build_from(p);
    }
    enum TINFO_STATUS { 
        TINFO_TYPE_INFER_SUCESS  =0x01,
        TINFO_TYPE_CHECK_SUCCESS =0x02,
        TINFO_TYPE_CHECK_FAIL = 0x0,
        TINFO_TYPE_INFER_FAIL = 0x80,
        TINFO_UNKNOWN_VAR_TYPE = 0x90,
        TINFO_UNKNOWN_PRED_TYPE = 0xA0,
    };
    bool tcheck();
    private:
    raw_prog &rp;
    bool infer; 
    environment &env;
    TINFO_STATUS tstat;
    std::vector<TINFO_STATUS> verrs;
    bool tinfer (const raw_rule&);
    bool tcheck (const raw_rule&) ;
    bool tcheck (const raw_term&);
    bool type_error(const char* e, lexeme l) {
        if(tstat == TINFO_TYPE_CHECK_SUCCESS)
            tstat = TINFO_TYPE_CHECK_FAIL;
    	input in((void*) 0, (size_t) 0);
	    return in.type_error(0, e, l[0]);
    }
    
};

struct bit_univ {
	enum { //should be compatible with typesystem's prim type
		CHAR_BSZ = 8,
		INT_BSZ = 16,
		SYM_BSZ = 8,
		VAR_BSZ = 8,
	};
	dict_t &d;
	environment &typenv;
    size_t char_bsz, int_bsz, sym_bsz, var_bsz;

	bit_univ(dict_t &_d, environment _e = environment(), size_t _cbsz = CHAR_BSZ, size_t _ibsz = INT_BSZ, 
	size_t _sbsz = SYM_BSZ, size_t _vbsz = VAR_BSZ): d(_d), typenv(_e), char_bsz(_cbsz),
	int_bsz(_ibsz), sym_bsz(_sbsz), var_bsz(_vbsz) { }
	
	size_t get_typeinfo(size_t n, const raw_term& rt, const raw_rule &rr );
	inline size_t pos(size_t bsz, size_t bit_from_right /*, size_t arg, size_t args */) const {
		DBG(assert(bit_from_right < bsz /*&& arg < args*/); )
		return (bsz - bit_from_right - 1); //* args + arg;
	}
	bool btransform( const raw_prog& rpin, raw_prog &rpout );
	bool btransform( const raw_rule& rrin, raw_rule &rrout );
	bool btransform( const raw_term& rtin, raw_term &rtout, const raw_rule &rr, raw_rule &rrout );
};


#endif
