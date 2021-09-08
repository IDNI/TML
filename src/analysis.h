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

typedef std::shared_ptr<class environment> spenvironment;
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

    const std::vector<typedecl>& search_pred(string_t &key, bool &found, int_t insize=-1) {
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
		INT_BSZ = 8,
		SYM_BSZ = 8,
		VAR_BSZ = 8,
	};
	dict_t &d;
    size_t bit_order;
    size_t char_bsz, int_bsz, sym_bsz, var_bsz;
    spenvironment ptypenv = nullptr;
    typedef std::vector<size_t> tab_args;
    /*
    raw_tables rtabs;
    
    bool get_raw_tables(){
         std::vector<string_t > tabnames = ptypenv->get_predicates();
        for( string_t &pname: tabnames ) {

            rtabs.insert({pname, tab_args()});
            auto typesig = ptypenv->lookup_pred(pname);
            for ( auto &targs: typesig )
                if(targs.is_primitive())
                    rtabs[pname].push_back(targs.pty.get_bitsz());
                else {
                    string_t sttype = lexeme2str(targs.structname.e);
                    rtabs[pname].push_back(
                        ptypenv->lookup_typedef(sttype).get_bitsz(*ptypenv));
                }
        }
        return true;
    }
    */
	bit_univ(dict_t &_d, size_t _bo, size_t _cbsz = CHAR_BSZ, size_t _ibsz = INT_BSZ,
	size_t _sbsz = SYM_BSZ, size_t _vbsz = VAR_BSZ): d(_d), bit_order(_bo), char_bsz(_cbsz),
	int_bsz(_ibsz), sym_bsz(_sbsz), var_bsz(_vbsz) {

        this->pos = [this](size_t a, size_t b, size_t c, size_t d, bit_univ::tab_args t)-> size_t{
					return this->pos_gen(a, b, c, d, t); };
     }
	size_t get_typeinfo(size_t n, const raw_term& rt, const raw_rule &rr );
	size_t pos_eqsz(size_t bsz, size_t bit_from_right , size_t arg, size_t args /*,tab_args rtab */ ) {
		DBG(assert(bit_from_right < bsz && arg < args); )
		return (bsz - bit_from_right - 1)* args + arg;
	}
    size_t pos_gen(size_t bsz, size_t bit_from_right , size_t arg, size_t args, tab_args rtab  ) {
		DBG(assert(bit_from_right < bsz && arg < args); )
		size_t pos = -1;
        size_t max_bits=0;
        for(size_t bits : rtab ) max_bits= std::max(max_bits, bits);
        for( size_t bit = 0; bit < max_bits; bit++)
            for( size_t a= 0 ; a<args ; a++) {
                if(bit < rtab[a]) pos++;
                if( bit == bit_from_right && arg == a) goto end;
            }
        
        end: return pos;
	}

    size_t pos_neqsz(size_t bsz, size_t bit_from_right , size_t arg, size_t args, tab_args rtab  ) {
        DBG(assert(bit_from_right < bsz && arg < args && args == rtab.size() && rtab[arg] == bsz); )
        DBG(COUT<< arg << " "<<  args << " "<<  bit_from_right << " "<< (bsz - bit_from_right -1) << " " <<bsz << " " );
        bools szsort(64); //max number of args <=64 in radix sorted form

        size_t skip = 0, cargs  = 0; // # of args with sz less than bit_rom_right;
        for( size_t i = 0 ; i <rtab.size(); i++) {
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
    size_t pos_default(size_t bsz, size_t bit_from_right , size_t arg, size_t args /*, tab_args rtab */ ) {
		DBG(assert(bit_from_right < bsz && arg < args); )
    	return (bsz - bit_from_right - 1); //* args + arg;
	}

    typedef std::function< size_t ( size_t , size_t , size_t , size_t, tab_args) > posfunc;
	posfunc pos;
    
    bool brev_transform( raw_term& bit_raw_term);
    bool brev_transform_check(const struct term &t, const struct table &tab);
	bool btransform( const raw_prog& rpin, raw_prog &rpout );
	private:
    bool btransform( const raw_rule& rrin, raw_rule &rrout );
	bool btransform( const raw_term& rtin, raw_term &rtout, const raw_rule &rr, raw_rule &rrout );
    public:
    template<class T>
    bool permuteorder(std::vector<T> &cont, size_t n, bool backward = false){
        static std::vector<int_t> ord, rord;
        if ( n == 0 ) return false;         
        std::vector<T> ocont = cont;
        if(ord.size() != cont.size()) {
            // should do more memoization,
            ord.resize(cont.size());
            rord.resize(cont.size());
            for( size_t i=0; i < ord.size(); i++)	ord[i] = i;
            while( n--  &&  std::next_permutation(ord.begin(), ord.end()));
            for( size_t i=0; i<rord.size(); i++)	rord[ord[i]] = i;
            DBG(COUT<<std::endl);
            for(int_t v: ord) { DBG(COUT<< v; ) }
        }
            // copy values from old array to cont
        DBG(COUT<< std::endl<<"B:"; std::for_each(cont.begin(), cont.end(), [](T val) { COUT<< val; } );)
        for(size_t i=0; i<cont.size(); i++)	cont[i] = ocont[!backward ? ord[i]: rord[i]];    
        DBG(COUT<< std::endl<<"A:"; std::for_each(cont.begin(), cont.end(), [](T val) { COUT<< val; } );)
        return true;
    }
};

#endif
