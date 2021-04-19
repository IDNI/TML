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

struct typestmt;
class environment {    
    //signatures 
    std::map<string_t, std::vector<typedecl> > predtype;
    std::map<string_t, structype> usertypedef;
    //contexts for vars
    std::map<string_t, primtype> context_prim_var;
    std::map<string_t, string_t> context_typedef_var;
    public:
    bool contains_pred(string_t key) const{
        return predtype.find(key) != predtype.end(); 
    }
    bool contains_typedef(string_t key) const{
        return usertypedef.find(key) != usertypedef.end() ; 
    }
    bool contains_prim_var(string_t var) const {
        return context_prim_var.find(var) != context_prim_var.end();
                
    }
    bool contains_typedef_var(string_t var) const {
        return context_typedef_var.find(var) != context_typedef_var.end() ;
    }
    bool build_from( raw_prog &rp  ) {
        return this->build_from(rp.vts);
    }
    bool build_from( const std::vector<struct typestmt> & );
    std::vector<typedecl> lookup_pred( string_t k  ){
        return predtype[k];
    }
    structype& lookup_typedef( string_t &k  ){
        return usertypedef[k];
    }
    bool addtocontext(string_t &var, primtype &pt ) {
        context_prim_var[var] = pt;
        return true;
    }
    bool addtocontext(string_t &var, structype &st ) {
        context_typedef_var[var] = lexeme2str(st.structname.e);
        return true;
    }
    bool addtocontext(string_t &var, string_t stname ) {
        context_typedef_var[var] = stname;
        return true;
    }
    void resetAll(){
        reset_context();
        predtype.clear();
        usertypedef.clear();
    }
    void reset_context(){
        context_prim_var.clear();
        context_typedef_var.clear();
    }
    primtype& lookup_prim_var( string_t var ){
        DBG(assert(context_prim_var.count(var)));
           return context_prim_var[var];

    }
    structype& lookup_typedef_var( string_t var ){
        DBG(assert( context_typedef_var.count(var)));
        return usertypedef[context_typedef_var[var]];
    }
};

class typechecker { 
    environment env;
    bool tcheck (const raw_rule& ) ;
    bool tcheck (const raw_term&);
    public:
    typechecker(raw_prog &p) {
        env.build_from(p);
     }
    bool tcheck (const raw_prog& );
};

struct bit_univ {
	enum { //should be compatible with typesystem's prim type
		CHAR_BSZ = 4,
		INT_BSZ = 4,
		SYM_BSZ = 4,
		VAR_BSZ = 4,
	};
	dict_t &d;
	size_t char_bsz, int_bsz, sym_bsz, var_bsz;

	bit_univ(dict_t &_d, size_t _cbsz = CHAR_BSZ, size_t _ibsz = INT_BSZ, 
	size_t _sbsz = SYM_BSZ, size_t _vbsz = VAR_BSZ): d(_d), char_bsz(_cbsz),
	int_bsz(_ibsz), sym_bsz(_sbsz), var_bsz(_vbsz) { }
	// innermost type definition of the nested program
	environment typenv;
	
	size_t get_typeinfo(size_t n, const raw_term& rt );
	inline size_t pos(size_t bsz, size_t bit_from_right /*, size_t arg, size_t args */) const {
		DBG(assert(bit_from_right < bsz /*&& arg < args*/); )
		return (bsz - bit_from_right - 1); //* args + arg;
	}
	bool btransform( const raw_prog& rpin, raw_prog &rpout );
	bool btransform( const raw_rule& rrin, raw_rule &rrout );
	bool btransform( const raw_term& rtin, raw_term &rtout );
};


#endif
