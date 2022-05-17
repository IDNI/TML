/*
 * typemanager.h
 *
 *  Created on: Mar 20, 2022
 *      Author: juan
 */

#ifndef SRC_TYPEMANAGER_H_
#define SRC_TYPEMANAGER_H_

#include "input.h"

typedef std::shared_ptr<class environment> spenvironment;

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
    // nested scope environmnet
    // tcheck connects these pointers.
    spenvironment parent= nullptr;
    std::vector<spenvironment > nested;

    public:
    environment(): parent(nullptr){}

    bool add_sig(string_t &predname, std::vector<primtype>& types) {
        if( contains_pred(predname) )    return false;
        std::vector<typedecl> instype;
        for( auto &pt : types) {
            typedecl  td;
            td.pty = pt;
            instype.push_back(td);
        }
        return predtype.insert({predname, instype}).second;
    }
    bool add_sig(string_t &predname, std::vector<typedecl>& types) {
        if( contains_pred(predname) )    return false;
        return predtype.insert({predname, types}).second;
    }
    std::vector<string_t> get_predicates() {
        std::vector<string_t> cont;
        for( auto it :predtype )
            cont.push_back(it.first);
        return cont;
    }
    void set_parent( spenvironment &_e) {
        parent = _e;
    }
    void set_nested( spenvironment &_e) {
        nested.emplace_back(_e);
    }

    const std::vector<typedecl> &search_pred(string_t &key, bool &found, int_t insize=-1) {
        auto it = predtype.find(key);

        if( it != predtype.end() ) {
            if(insize < 0 ) found = true;
            else {
                auto &types = it->second;
                int_t cursz = 0;
                for( auto &it : types)
                    if(it.is_primitive())
                        cursz += it.pty.get_bitsz();
                    else {
                        string_t st = lexeme2str(it.structname.e);
                        cursz += this->lookup_typedef(st).get_bitsz(*this);
                    }
                if(cursz == insize) found = true;
            }
        }
        if( found == false) {
            for( auto &nest: nested) {
                auto &ret = nest->search_pred(key, found, insize);
                if(found) return ret;
            }
        }
        return it->second;
    }
    bool contains_pred(string_t &key) const{
        if(predtype.find(key) != predtype.end()) return true;
        return parent ? parent->contains_pred(key) : false;
    }
    bool contains_typedef(string_t &key) const{

        if( usertypedef.find(key) != usertypedef.end() ) return true;
        return parent ? parent->contains_typedef(key) : false;
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
        for(auto &it : predtype){
        	ret.append("Signature for table ");
            ret.append(to_string(it.first) + " < ");
            for( auto &s: it.second)
                ret.append(s.to_print()+" ");
            ret.append(">");
            ret.append("\n");
        }
        return ret;
    }
    bool build_from( const raw_term &rt, bool infer);
    bool build_from( const raw_rule &rr);
    bool build_from( const raw_prog &rp  );
    bool build_from( const std::vector<struct typestmt> & );
    const std::vector<typedecl>& lookup_pred( const string_t k  )  const {
        auto it =  predtype.find(k);
        if( it == predtype.end() ) {
            if(parent) return parent->lookup_pred(k);
            else throw_runtime_error("type not found");
        }

        return it->second;
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

//-----------------------------------------------------------------------------

class typemanager {

public:
	typemanager() {}
    ~typemanager() {}

    bool type_check(raw_prog &rp) {
    	if (env.build_from(rp)) return true;
    	else return tcheck(rp);
    }
    bool infer = true;
    environment env;

private:
    enum TINFO_STATUS {
        TINFO_TYPE_INFER_SUCESS  =0x01,
        TINFO_TYPE_CHECK_SUCCESS =0x02,
        TINFO_TYPE_CHECK_FAIL = 0x0,
        TINFO_TYPE_INFER_FAIL = 0x80,
        TINFO_UNKNOWN_VAR_TYPE = 0x90,
        TINFO_UNKNOWN_PRED_TYPE = 0xA0,
    } tstat = TINFO_TYPE_CHECK_FAIL;

    std::vector<TINFO_STATUS> verrs;
    bool tinfer(const raw_rule&);
    bool tinfer(const raw_form_tree &);
    bool tcheck(const raw_rule&);
    bool tcheck(const raw_form_tree &prft);
    bool tcheck(const raw_term&);
    bool tcheck(const raw_prog&);
    bool type_error(const char* e, lexeme l) {
        if(tstat == TINFO_TYPE_CHECK_SUCCESS)
            tstat = TINFO_TYPE_CHECK_FAIL;
    	input in((void*) 0, (size_t) 0);
	    return in.type_error(0, e, l[0]);
    }
};

#endif /* SRC_TYPECHECKER_H_ */
