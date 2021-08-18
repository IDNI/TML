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


#include <algorithm>
#include <vector>
#include "analysis.h"
#include "dict.h"
#include "term.h"
#include "tables.h"


bool bit_univ::btransform( const raw_prog& rpin, raw_prog &rpout ){
	bool ret = true;

	typenv = (const_cast<raw_prog&>(rpin)).get_typenv();
	// set the same environment for the output raw bit prog 
	rpout.set_typenv(typenv);
	rpout.g = rpin.g;
	get_raw_tables();

	for( const raw_rule &rr : rpin.r)
		rpout.r.emplace_back(), ret &= btransform(rr, rpout.r.back());
	for( const raw_prog &rp : rpin.nps)
		rpout.nps.emplace_back(), ret &= btransform(rp, rpout.nps.back());	
	return ret;
}

bool bit_univ::btransform( const raw_rule& rrin, raw_rule &rrout ){
	bool ret = true;
	for( const raw_term &rt : rrin.h )
		rrout.h.emplace_back(), ret &= btransform(rt, rrout.h.back(), rrin, rrout);
	for( const auto &vrt : rrin.b) {
		rrout.b.emplace_back();
		for( const raw_term &rt : vrt)
			rrout.b.back().emplace_back(), 
			ret &= btransform(rt, rrout.b.back().back(), rrin, rrout);	
	}
	return ret;
}

size_t bit_univ::get_typeinfo(size_t n, const raw_term &rt, const raw_rule &rr) {
	
	DBG(assert(rt.e.size()>n && (int_t)n >=0 && rr.varctx.get()) );

	if(rt.extype == raw_term::ARITH || rt.extype == raw_term::EQ || rt.extype == raw_term::LEQ) {
		string_t str = lexeme2str(rt.e[n].e);
		if( rt.e[n].type == elem::VAR ) {
			if( rr.varctx.get()->contains_prim_var(str) )
				return rr.varctx.get()->lookup_prim_var(str).get_bitsz();
			else if( rr.varctx.get()->contains_typedef_var(str) ) {
				//todo for struct types.
				//should struct types ever have arithmetic operation, no!
				DBG(assert(false));
				this->typenv.lookup_typedef_var(str).get_bitsz(typenv);
			}
			else {
				//should this case ever happen when ctx does not know the type of var? no.
				// typecheck should have failed before.
				DBG(assert(false));
				return VAR_BSZ;
			}
		}
		else if ( rt.e[n].type == elem::NUM ) {
			// get the type info based on nearest var
			int_t i = n;
			while(i>=0 && i < (int_t)rt.e.size() && 
				(rt.e[i].type != elem::VAR ||rt.e[(int_t)rt.e.size()-i-1].type != elem::VAR)) i++;
			if(i>=0 && i < (int_t)rt.e.size())
				return get_typeinfo(i, rt, rr); 
		
			return INT_BSZ;
		}
	}
	else if( rt.extype == raw_term::REL || rt.extype == raw_term::BLTIN) {
		string_t reln = lexeme2str(rt.e[0].e);
		if( typenv.contains_pred(reln)) {
			auto &targs = typenv.lookup_pred(reln);	
			//only for arguments
			if(n>1 && n < rt.e.size()-1) {
				if(targs[n-2].is_primitive())
					return targs[n-2].pty.get_bitsz();
				else {
					DBG(assert(targs[n-2].is_usertype()));
					string_t stn = lexeme2str(targs[n-2].structname.e);
					if(typenv.contains_typedef( stn)){
						return typenv.lookup_typedef(stn).get_bitsz(typenv);
					}
					o::err()<< "No type found : "<<targs[n-2].structname<<std::endl;
				}
			} 
			
		}
		else {
			//when types are not specified, go default
			if(	rt.e[n].type == elem::SYM || rt.e[n].type == elem::CHR || 
				rt.e[n].type == elem::VAR || rt.e[n].type == elem::NUM )
				return INT_BSZ;
		}
	}
	// for everything else
	return 0;
}
bool bit_univ::brev_transform_check(const term &t, const table &tab){

	const lexeme & pred = d.get_rel(tab.s.first);
	const std::vector<typedecl> &vt = this->typenv.lookup_pred(lexeme2str(pred));
	auto rtab = rtabs.find(lexeme2str(pred))->second;
	int_t val = 0;
	//for symbols, check if the value is in dict
	for( int_t arg=0; arg < rtab.size(); arg++)
		if( vt[arg].is_primitive() && vt[arg].pty == primtype::SYMB) {
			size_t  bitsz = vt[arg].pty.get_bitsz();
			val = 0;				
			//construct arg value from bits using pos					
			for( int_t k = 0; k < bitsz; k++) {
				int_t ps = pos( bitsz, k, arg, rtab.size(), rtab);
				//DBG(COUT<<ps<<std::endl);	
				DBG(assert(ps < t.size()));
				val |= t[ps] << k;
			}
			if(! d.is_valid_sym_val(val)) return false;
		}
		
	return true;
}

//inplace transformation of bit raw term to normal as per type_env/
bool bit_univ::brev_transform( raw_term &rbt ){
	
	string_t str = lexeme2str(rbt.e[0].e);
	const std::vector<typedecl> &vt = this->typenv.lookup_pred(str);
	auto rtab = this->rtabs.find(str)->second;
	if(vt.size() == 0 ) return false;
	int_t bitsz = -1;
	int_t val = 0, arg = 0,  args = vt.size();
	// save bits and clear from rbt
	std::vector<elem> rbits{ rbt.e.begin()+2, rbt.e.end()-1 };
	rbt.e.erase(rbt.e.begin()+2, rbt.e.end()-1);
	for(typedecl td: vt ) {
		if( td.is_primitive() ) {
			bitsz =  td.pty.get_bitsz();
			val = 0;				
			//construct arg value from bits using pos					
			for( int_t k = 0; k < bitsz; k++) {
				int_t ps = pos( bitsz, k, arg, args, rtab);
				//DBG(COUT<<ps<<std::endl);	
				val |= rbits[ps].num << k;
			}
			elem el;
			if( td.pty.ty == primtype::UINT )
				el = elem(val);
			else if ( td.pty.ty == primtype::UCHAR )
				el = elem((char32_t) val);
			else if ( td.pty.ty == primtype::SYMB )   // should differentiate from STR
				el = elem(elem::SYM, this->d.get_sym(val) );

			rbt.e.insert(rbt.e.begin() + 2 + arg, el);
			arg++;
		}
		else { } //structtypes userdef
	}
	return true;
}


bool bit_univ::btransform(const raw_term& rtin, raw_term& rtout, const raw_rule &rr, raw_rule &rrout){
	bool ret = true;
	rtout.neg = rtin.neg;	
	if( rtin.extype == raw_term::REL || rtin.extype == raw_term::BLTIN) {	
		int_t args = rtin.e.size() == 1 ? 0: rtin.e.size()-3;	
		DBG(assert(args == rtin.arity[0]));
		
		string_t pname = lexeme2str(rtin.e[0].e);
		tab_args targs = rtabs.find(pname)->second;
		// getting total bits for the table/predicate
		size_t totalsz = 0;
		for( size_t asz : targs  )	totalsz += asz;
		std::vector<elem> bitelem(totalsz);
		DBG(COUT<<"size for "<<rtin.e[0].e<< "="<<totalsz<<std::endl);
		for(size_t n= 0 ;n < rtin.e.size(); n++ ) {
			const elem& e = rtin.e[n];
			// for predicate rel name, keep as it is
			if( n == 0 ) { rtout.e.emplace_back(e); continue; }		
			// get bit size of the given elem and convert to bit representation/
			size_t bsz = get_typeinfo(n, rtin, rr);
			if( bsz <=0 ) { rtout.e.emplace_back(e); continue; }
			int_t symbval = 0;
			for (size_t k = 0; k != bsz; ++k) {
				
				int_t ps = pos(bsz, k, n-2, args, targs);
				DBG(COUT<< ps<<std::endl;assert(ps < bitelem.size()));
			/*	//dynamically grow bitsiz
				if(ps >= bitelem.size()) {
					int_t incr = ps - bitelem.size() + 1 ;
					while(incr--) bitelem.emplace_back(false);
				} */			
				switch(e.type) {
					case elem::NUM: bitelem[ps] = bool(e.num & (1<<k)); break;
					case elem::CHR: bitelem[ps] = bool(e.ch & (1<<k)); break;
					case elem::VAR: { 
						string_t temp = lexeme2str(e.e);
						// making new bit vars and avoiding conflict 
						temp.append(to_string_t("_").append(to_string_t((int_t)k)));
						bitelem[ps] = {elem::VAR, d.get_lexeme(temp)};
						break; 
					}
					case elem::STR:
					case elem::SYM: {
						if( k == 0 ) symbval = d.get_sym(e.e);
						bitelem[ps] = bool(symbval & (1<<k)); 
						break;
					}
					default: DBG( COUT<<e<<std::endl; assert(false)); break;
				}
			}
	//		permuteorder(bitelem, bit_order);	
		}
		//insert before last enclosing paranthesis
		if(bitelem.size()) rtout.e.insert(rtout.e.end()-1, bitelem.begin(), bitelem.end());
		ret &= rtout.calc_arity(0);
	}
	else if ( rtin.extype == raw_term::ARITH || rtin.extype == raw_term::EQ || rtin.extype == raw_term::LEQ) {
		std::vector<std::vector<elem>> vbit;
		for(size_t n= 0 ;n < rtin.e.size(); n++ ) {
			const elem& e = rtin.e[n];
			string_t str = lexeme2str(e.e);
			size_t bsz = get_typeinfo(n, rtin, rr);
			switch( e.type ){
				case elem::VAR: vbit.emplace_back(); 
								vbit.back().resize(bsz);
								for( size_t k= 0; k !=bsz ; k++){
									string_t temp = str;
									temp.append(to_string_t("_").append(to_string_t((int_t)k)));
									vbit.back()[k] = {elem::VAR, d.get_lexeme(temp)};
								}
								break;
				case elem::NUM:
								vbit.emplace_back(); 
								vbit.back().resize(bsz);
								for( size_t k= 0; k !=bsz ; k++)
									vbit.back()[k] = bool(e.num & (1<<k));
								break;
				case elem::ARITH:
				case elem::EQ:
				case elem::LEQ: // user size of prev var
								bsz = vbit.back().size();
								vbit.emplace_back(); 
								vbit.back().resize(bsz);
								for( size_t k= 0; k !=bsz ; k++)
									vbit.back()[k] = e;
								
								break;
				default : DBG(COUT<<rtin<<std::endl); assert(false);
			}	
		}
		if( vbit.size()) rrout.b.back().pop_back(); // so that rrout is not there

		for( size_t j=0 ; j < vbit[0].size(); j++) {
			rrout.b.back().emplace_back();
			for( size_t i =0 ; i< vbit.size(); i++) 
				rrout.b.back().back().e.push_back(vbit[i][j]);
			
			raw_term &out = rrout.b.back().back();
			out.extype = rtin.extype;
			if(out.extype == raw_term::EQ || out.extype == raw_term::LEQ)
				out.arity = {2}; 			
			DBG(COUT<<std::endl<<out);
		}
	}
	return ret;
}

size_t structype::calc_bitsz(const std::vector<typestmt> &types){	
	size_t bsz=0;
	static std::set<elem> done;
	if(done.find(structname) != done.end()) { 
		DBG(COUT<<"Recursive type "<< structname <<" not defined completely" <<std::endl);
		return bsz;
	}
	done.insert(structname);

	for( auto md : this->membdecl) {
			if(md.is_primitive()) 
				bsz += md.pty.get_bitsz()*md.vars.size();
			else {	// do for struct;
				for( auto rit : types)
					if( rit.rty.structname == md.structname  )
						bsz +=  rit.rty.get_bitsz( types ) * md.vars.size();
			}
		}
	done.erase(this->structname);
	DBG(COUT<<std::endl<<structname << "calculated bits:"<<bsz);
	return bsz;
}

size_t structype::calc_bitsz(environment &env){
	
	size_t bsz = 0;
	static std::set<elem> done;
	if(done.find(structname) != done.end()) { 
		DBG(COUT<<"Recursive type "<< structname <<" not defined completely" <<std::endl);
		return bsz = 0 ;
	}
	done.insert(structname);
	for( auto md : this->membdecl) {
			if(md.is_primitive()) 
				bsz += md.pty.get_bitsz()*md.vars.size();
			else {	// do for struct;
					string_t stctnm = lexeme2str(md.structname.e) ;
					if( env.contains_typedef(stctnm)  ) 
						bsz +=  env.lookup_typedef(stctnm).get_bitsz(env) * md.vars.size();
			}
		}
	done.erase(this->structname);
	DBG(COUT<<std::endl<<structname << "calculated bits:"<<bsz);
	return bsz;
}
bool primtype::parse( input* in , const raw_prog& /*prog*/) {

	static const std::map<std::string, _ptype> tym = {
		{ "int",  UINT  },
		{ "char", UCHAR },
		{ "sym",  SYMB  }
	};	
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;
	
	if ( !el.parse(in) ||  el.type != elem::SYM)
		return pos = curr, false;

	std::string st = to_string(lexeme2str(el.e));
	auto it = tym.find(st);
	if( it == tym.end()) return pos = curr, false;

	ty = it->second;
	if( ty == primtype::UINT) {
		if( *l[pos][0] == ':') {
			pos++;
			elem b;
			if( b.parse(in) && b.type == elem::NUM)
				bsz = b.num;
			else return pos = curr, false;
		}
	}
	return true;
}

bool structype::parse(input *in, const raw_prog& prog){
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;

	if( (l[pos][1] - l[pos][0]) != 6 || strncmp(l[pos++][0],"struct", 6) != 0 ) goto FAIL;
	if( !structname.parse(in) || structname.type != elem::SYM ) goto FAIL;
	if(*l[pos++][0] != '{') goto FAIL;

	while( pos < l.size() &&  *l[pos][0] != '}') {
		membdecl.emplace_back();
		if(false == membdecl.back().parse(in, prog)) {
				in->parse_error(l[pos][0], "Incorrect member declaration", l[pos]);
				goto FAIL;
			}
		if( *l[pos][0] == '.') { pos++; }
		else goto FAIL;
	}
	if(*l[pos++][0] == '}') return true;

	FAIL: 
	in->parse_error(l[pos][0], "Incorrect struct declaration", l[pos]);
	return pos=curr, false;
}
bool typedecl::parse( input* in , const raw_prog& prog, bool notparam){
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;
	if ( pty.parse(in, prog) || (structname.parse(in) && structname.type == elem::SYM) ) {
		for( ;pos < l.size() ; )  {
			vars.emplace_back();
			if( ! vars.back().parse(in) || vars.back().type != elem::VAR ) goto FAIL;
			if( !notparam) break; // if parameter then only one var for one type
			if (*l[pos][0] == ',') pos++; else break; 
		}
		if(vars.size())	return true;
	}
	else if ( !notparam ) return true; // for void parameters in predtype declarattion

	FAIL:
	in->parse_error(l[pos][0], "Incorrect var declared ", l[pos]);
	return pos = curr, false;
}

bool typestmt::parse( input* in , const raw_prog& prog){
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;
	if( (l[pos][1]-l[pos][0]) == 8 && strncmp(l[pos][0],"predtype", 8) == 0 ) {
		pos++;
		if( !reln.parse(in) || reln.type != elem::SYM ) goto FAIL;
		if(*l[pos++][0] != '(') goto FAIL;
		for( ;pos < l.size() && (*l[pos][0] != ')'); ) {
			typeargs.emplace_back();
			if( !typeargs.back().parse(in, prog, false) ) goto FAIL;
			if (*l[pos][0] == ',') pos++; else break; 
		}
		if(*l[pos++][0] != ')' ||  *l[pos++][0] != '.'   ) goto FAIL;
		return true;
	}
	else if ( (l[pos][1]-l[pos][0]) == 6 && strncmp(l[pos][0],"struct", 6) == 0  ) {
		if( rty.parse(in, prog)) return true;
		if(*l[pos++][0] != '.' ) goto FAIL;
	}
	FAIL:
	return pos=curr, false;
}

bool environment::build_from( const std::vector<typestmt> & vts) {
	
	resetAll();
	for( auto it : vts){
		if( it.is_predicate()) { // this is predicate declaration
			if( predtype.find(lexeme2str(it.reln.e)) != predtype.end() )
				return input().type_error(" Predicate redefined.", it.reln.e), false;
			predtype.insert({ lexeme2str(it.reln.e), it.typeargs  });		
		}
		else if( it.is_typedef()) { // this is new type definitinon
			if( usertypedef.find(lexeme2str(it.rty.structname.e)) != usertypedef.end() )
				return input().type_error(" Repeated typedef.", it.rty.structname.e), false;
			usertypedef.insert( { lexeme2str(it.rty.structname.e), it.rty });					}
	}
	if( predtype.size() || usertypedef.size()) return true;
	return false;
}
// infers from given predicates the type signature of relation while
// making use of var context and updates only the pred_type of env.
// returns true if new signature found. Does not update context of vars
// for arith terms, just ensures that all vars have types and returns true	std::vector<typedecl> targs;
// option to change return val; (1) either on new signature, or (2) if everything inferrable.
// currently (2)

bool environment::build_from( const raw_term &rt, bool infer=false){
	string_t str = lexeme2str(rt.e[0].e);

	if( this->contains_pred(str)){
		// know types already, just try to update var context.
		const std::vector<typedecl> &targs= this->lookup_pred(str);
		bool updated =false;
		for( size_t i=2; i < rt.e.size()-1; i++ ){
			if(rt.e[i].type== elem::VAR ) {
				str = lexeme2str(rt.e[i].e);
				//context already knows var types
					if (this->contains_prim_var(str) ){
						//DBG(assert( this->lookup_prim_var(str) == targs[i-2].pty));
						// override type definition
						updated |= this->addtocontext(str, targs[i-2].pty );
					}
					else if( this->contains_typedef_var(str)) {
						//	DBG(assert( this->lookup_typedef_var(str).structname == targs[i-2].structname));
					}
				//context does not know..so now populate from signature
					else if( targs[i-2].is_primitive()){
						updated |= this->addtocontext(str, targs[i-2].pty);
					}
					else if( targs[i-2].is_usertype()){
						updated |= this->addtocontext(str, lexeme2str(targs[i-2].structname.e));
					}
			}
		}
		return updated;
	}
	std::vector<typedecl> targs;
	size_t st=0, end=rt.e.size();
	bool bknown = true;  // assume all args types are determinable 
	if(rt.extype == raw_term::REL || rt.extype == raw_term::BLTIN) st = 2, end = rt.e.size()-1;
	for( size_t i= st ; bknown && i < end; i++) {
		str = lexeme2str(rt.e[i].e);
		if(rt.extype == raw_term::REL || rt.extype ==raw_term::BLTIN) {
			switch(rt.e[i].type) {
				case elem::NUM:  targs.emplace_back(), targs.back().pty.ty = primtype::UINT;break;
				case elem::CHR:  targs.emplace_back(), targs.back().pty.ty = primtype::UCHAR;break;
				case elem::SYM: 
				case elem::STR: targs.emplace_back(), targs.back().pty.ty = primtype::SYMB;break;
				case elem::VAR:						
								if(infer && this->contains_prim_var(str)) {						
										targs.emplace_back(),
										targs.back().pty = this->lookup_prim_var(str);
								}
								else if( infer && this->contains_typedef_var(str) ){
										targs.emplace_back(),
										targs.back().structname = rt.e[i];
								}
								else bknown = false;
								break;
				default: break; // all arith/op/ etc
			}
		}
		else if(rt.extype == raw_term::ARITH || rt.extype == raw_term::EQ ||
												rt.extype == raw_term::LEQ ){ 
				if(rt.e[i].type== elem::VAR && !(this->contains_prim_var(str) ||
					this->contains_typedef_var(str) ))	bknown = false;
		}
		else { DBG(COUT<<rt<<std::endl; assert(false);)  } 
	}

	if(bknown){
			//only insert signature for relations.
			if( rt.extype == raw_term::REL || rt.extype == raw_term::BLTIN)
		 		str = lexeme2str(rt.e[0].e),
				predtype.insert( { lexeme2str(rt.e[0].e), targs } );
			//for others, just enough to say types are known
	}
	// the context does not have types, try to infer from  nearest vars/operations
	else {
		//Todo:
		if(rt.extype == raw_term::ARITH || rt.extype == raw_term::EQ ||
												rt.extype == raw_term::LEQ ){
			bool lastb = false;
			primtype lastp;
			//TOD0: need to have a consistent way of selecting type
			// without ordering effect, it should be some least abstract
			// type. For now, pick the first known type and assing to typeless
			std::vector<string_t> notypv;
			bool hasnum = false;
			for( size_t i=0; i < rt.e.size(); i++ )
				if(rt.e[i].type== elem::VAR ) {
					str = lexeme2str(rt.e[i].e);
						if (this->contains_prim_var(str) && !lastb)
							lastp = this->lookup_prim_var(str), lastb =true;
						else if( this->contains_typedef_var(str)) ;//TOD): ;
						else notypv.push_back(str);
				}
				else if ( rt.e[i].type == elem::NUM){
					hasnum = true;
				}
			if(lastb) for(string_t var: notypv)	this->addtocontext(var, lastp);
			else if( hasnum) for(string_t var: notypv)	this->addtocontext(var, primtype(primtype::UINT));
			
			bknown = lastb | hasnum; 
		}
	}

	return bknown;
}

bool environment::build_from( const raw_prog &rp  ) {
	// populate from user declsared static types if any
	return this->build_from(rp.vts);
}

// try to infer from given terms of rules using context
// returns true if the new signature found
bool typechecker::tinfer( const raw_rule& rr){
	
	bool ret = false;
	std::stringstream ss;
	context old = *(rr.get_context().get());
	env.get_context() = old;
	for (const raw_term &ht : rr.h){
		string_t str = lexeme2str(ht.e[0].e);
		if(!env.build_from(ht, infer) ){
			ss<<"Could not infer types from"<<ht,
			type_error(ss.str().c_str(), ht.e[0].e );
			ss.str("");
		}
		else ret = true;
	}
	for (auto &it : rr.b)
		for (const raw_term &bt : it) {
			string_t str = lexeme2str(bt.e[0].e);
			if(!env.build_from(bt, infer) ){
				ss<<"Could not infer types from predicate "<<bt,
				type_error(ss.str().c_str(), bt.e[0].e );
				ss.str("");
				ss.clear();
			}
			else ret = true;
		}

	if(ret && ( old != env.get_context()))
		return *(rr.get_context().get()) = env.get_context(), true;
	else return false;
}
bool typechecker::tcheck(){
	bool ret = true;
	std::vector<TINFO_STATUS> vrinfo(rp.r.size());
	//typecheck and build var context for each rule
	for (size_t i=0; i < rp.r.size(); i++) {
		if(( tcheck(rp.r[i]))) {	
			//see if there is any need for inference.		
			if(std::count_if(verrs.begin(), verrs.end(), [](TINFO_STATUS st){
				return st == TINFO_UNKNOWN_PRED_TYPE || st == TINFO_UNKNOWN_VAR_TYPE;
				})){
					vrinfo[i] = TINFO_UNKNOWN_PRED_TYPE; 
				}
			else vrinfo[i] = TINFO_TYPE_CHECK_SUCCESS; 
		}
		else ret = false, vrinfo[i] = TINFO_TYPE_CHECK_FAIL; // type_check fails.
	}
	
	if( ret && infer ) {	
		// only try inference when typecheck for any rule does not fail
		_BEG:
		bool sigupdated = false;
		if(rp.r.size())	DBG(COUT<<std::endl<< "Attempt to infer and typecheck rules with typeless terms \n");
		auto lastinfo = vrinfo;
		for (size_t i=0; i < rp.r.size(); i++) {
			if( vrinfo[i] == TINFO_UNKNOWN_PRED_TYPE) {
				if( tinfer(rp.r[i]) ) { // new signature added probably
					sigupdated = true;
				}
			}
		}
		for (size_t i=0; i < rp.r.size() ; i++) {
			if( vrinfo[i] == TINFO_UNKNOWN_PRED_TYPE) {
				if( tcheck(rp.r[i]) ) {	
					if(std::count_if(verrs.begin(), verrs.end(), [](TINFO_STATUS st){
						return st == TINFO_UNKNOWN_PRED_TYPE || st == TINFO_UNKNOWN_VAR_TYPE;
						})){
								vrinfo[i] = TINFO_UNKNOWN_PRED_TYPE; 
						}
					else vrinfo[i] = TINFO_TYPE_CHECK_SUCCESS;
				}
				else ret =false, vrinfo[i] = TINFO_TYPE_CHECK_FAIL;
			}
		}
		if(lastinfo != vrinfo || sigupdated ) { sigupdated =false; goto _BEG; }
		else if(rp.r.size()) DBG(COUT<<"converging inference" <<std::endl);
	}
	if(ret) {
		if(std::count_if(vrinfo.begin(), vrinfo.end(), [](TINFO_STATUS st){
			return st == TINFO_UNKNOWN_PRED_TYPE || st == TINFO_UNKNOWN_VAR_TYPE || 
					st == TINFO_TYPE_CHECK_FAIL;
			})){
					ret = false; 
			}
	}

	for( auto &nrp: rp.nps){
		typechecker tc(nrp, infer);
		ret &= tc.tcheck() ;
	}
	DBG(COUT<<env.to_print());
	for( size_t i =0 ; i <rp.r.size(); i ++)
		DBG(COUT<<(rp.r[i].get_context().get()?rp.r[i].get_context().get()->to_print():""));
	return ret;
}

bool typechecker::tcheck( const raw_term &rt){
	tstat = TINFO_TYPE_CHECK_SUCCESS;
	string_t str = lexeme2str(rt.e[0].e);

	std::stringstream ss;
	if( rt.extype == raw_term::REL || rt.extype == raw_term::BLTIN ) {
		if( env.contains_pred(str)){	
			auto &typeparams = env.lookup_pred(str);
			if( typeparams.size() != size_t(rt.arity[0])) 
				return 	ss<<"Expected arity for " << rt << " is " <<typeparams.size(),
						type_error(ss.str().c_str(), rt.e[0].e), false;
			
			size_t argc = 2;
			for( auto &typexp: typeparams) {
				if( typexp.is_primitive() ) {
					switch ( rt.e[argc].type) {
						case elem::NUM: 
							if( typexp.pty.ty != primtype::_ptype::UINT)  
								return 	ss<<"Expected type for argument "<<argc -1<<":" << rt.e[argc].num << " is ",
										ss << typexp.pty.to_print() <<" in predicate "<<rt,
										type_error(ss.str().c_str(), rt.e[argc].e), false;
							else {
								uint64_t maxval =  ( ((uint64_t)0x1 <<typexp.pty.get_bitsz())-1);
								if( rt.e[argc].num > maxval || typexp.pty.get_maxbits() < (int_t)typexp.pty.get_bitsz())
								return 	ss<< rt.e[argc].num << " exceeds max size for ",
										ss << typexp.pty.to_print() <<" in predicate "<<rt,
										type_error(ss.str().c_str(), rt.e[argc].e), false;	
							}
							break;
						case elem::CHR:  
							if( typexp.pty.ty != primtype::_ptype::UCHAR)  
								return 	ss<<"Expected type for argument "<<argc -1<<":" << to_string(to_string_t(rt.e[argc].ch))<<" is ",
										ss << typexp.pty.to_print() <<" in predicate "<<rt,
										type_error(ss.str().c_str(), rt.e[argc].e), false;
							break;
						case elem::SYM:   
							if( typexp.pty.ty != primtype::_ptype::SYMB)  
								return 	ss<<"Expected type for argument "<<argc -1<<":"  << rt.e[argc].e << " is ",
										ss << typexp.pty.to_print() <<"in predicate "<<rt,
										type_error(ss.str().c_str(), rt.e[argc].e), false;

							break;
						case elem::VAR: {
								string_t var = lexeme2str(rt.e[argc].e);
								if( env.contains_prim_var(var) ) {
									primtype &pt =  env.lookup_prim_var(var);
									if( typexp.pty != pt ) {
										ss<< "Type "<<  pt.to_print()<< " of "<<rt.e[argc].e << " does not match expected type "; 
										ss<< typexp.pty.to_print() << " in predicate " <<rt;
										return type_error(ss.str().c_str(), rt.e[argc].e ), false;	
									}
								}
								else env.addtocontext(var, typexp.pty );
							}
							break;
						default: break;
					}
				}
				else if ( typexp.is_usertype()) {
					str = lexeme2str(typexp.structname.e);
					if(!env.contains_typedef(str))
							return ss << "Type "<<  typexp.structname.e << " of "<<rt.e[argc].e << " is undefined", 
									type_error(ss.str().c_str(), rt.e[argc].e), false; 

					string_t var = lexeme2str(rt.e[argc].e);
					if( env.contains_typedef_var(var) ) {
						structype &st =  env.lookup_typedef_var(var);
						if( typexp.structname != st.structname ) {
							ss<< "Type "<<  st.structname.e << " of "<<rt.e[argc].e << " does not match expected type "; 
							ss<< typexp.structname.e << " in predicate " <<rt;
							return type_error(ss.str().c_str(), rt.e[argc].e ), false;	
						}
					}
					else env.addtocontext(var, str );
		
				}
				argc++;
			}
		}
		else { // the predicate signatures are not specified and found
			ss<< "Type signature for predicate"<<rt<< " not found "; 
			tstat = TINFO_UNKNOWN_PRED_TYPE;
			return type_error(ss.str().c_str(), rt.e[0].e ), false;	
		}
	}
	else if ( rt.extype == raw_term::EQ || rt.extype == raw_term::LEQ || rt.extype == raw_term::ARITH ) {
		// for arith, eq, leq, iterate over vars to ensure same type
		primtype lastp;
		bool last =false;

		for( const elem &e : rt.e){
			str = lexeme2str(e.e);
			if( e.type == elem::VAR ) {	
				if( env.contains_prim_var(str) ){
					if(last == false)
						lastp = env.lookup_prim_var(str), last = true;
					else if( lastp != env.lookup_prim_var(str) ) 
						return ss<< "Type "<< lastp.to_print()<<" of "<< to_string(str) << " does not match other var type in term " <<rt,
						type_error(ss.str().c_str(), rt.e[0].e ), false;
					
					if( rt.extype == raw_term::ARITH && last && lastp.ty != primtype::_ptype::UINT )
						return ss<< "Type "<< lastp.to_print()<<" of "<< to_string(str) << " cannot be applied to arithmetic terms  " <<rt,
						type_error(ss.str().c_str(), rt.e[0].e ), false;
				}
				else if (env.contains_typedef_var(str) ) {
					ss<< "Type of complex type var "<<str.c_str()<< " does not work with comparison and arithmetic operator"; 
					return type_error(ss.str().c_str(), rt.e[0].e ), false;	
				}
				else {
					tstat = TINFO_UNKNOWN_VAR_TYPE;
					ss<< "Type for var "<<str.c_str()<< " not found or specified "; 
					return type_error(ss.str().c_str(), rt.e[0].e ), false;	
				}
			}
		}
	}
	return true;
}

bool typechecker::tcheck( const raw_rule &rr){
	std::stringstream ss;
	env.reset_context();
	if( rr.get_context().get() != nullptr)
		env.get_context() = *(rr.get_context().get());
	verrs.clear();
	for (const raw_term &ht : rr.h)
		if(!tcheck(ht)) verrs.push_back(tstat);
	
	for (auto &it : rr.b)
		for (const raw_term &bt : it)
			if(! tcheck(bt)) verrs.push_back(tstat);
	// update newly discovered var context for rule only if no static type errors		
	if (std::count(verrs.begin(), verrs.end(), TINFO_TYPE_CHECK_FAIL ) == 0)
		return rr.update_context(std::make_shared<context>(env.get_context())), true;
	
	return false;

}
