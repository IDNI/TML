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
#include "typemanager.h"

namespace idni {

bool typemanager::tinfer( const raw_form_tree &rft){

	bool ret = true;
	if( rft.type == elem::NONE ) {
		string_t str = lexeme2str(rft.rt->e[0].e);
		if(!env.build_from(*rft.rt, infer) ){
			std::stringstream ss;
			ss<<"Could not infer types from predicate "<<*rft.rt,
			type_error(ss.str().c_str(), rft.rt->e[0].e );
			ss.str("");
			ss.clear();
			ret = false;
		}
	}
	if(rft.l != nullptr ) ret &= tinfer(*rft.l);
	if(rft.r != nullptr ) ret &= tinfer(*rft.r);

	return ret;
}
// try to infer from given terms of rules using context
// returns true if the new signature found
bool typemanager::tinfer( const raw_rule& rr){

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
	if( rr.is_form()) ret = tinfer(*rr.prft);
	else {
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
	}
	if(ret && ( old != env.get_context()))
		return *(rr.get_context().get()) = env.get_context(), true;
	else return false;
}

bool typemanager::tcheck(const raw_prog &rp) {
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
		if(rp.r.size())	{DBG(COUT<<std::endl<< "Attempt to infer and typecheck rules with typeless terms \n");}
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
		else if(rp.r.size()) {DBG(COUT<<"converging inference" <<std::endl);}
	}
	if(ret) {
		if(std::count_if(vrinfo.begin(), vrinfo.end(), [](TINFO_STATUS st){
			return st == TINFO_UNKNOWN_PRED_TYPE || st == TINFO_UNKNOWN_VAR_TYPE ||
					st == TINFO_TYPE_CHECK_FAIL;
			})){
					ret = false;
			}
	}
	if(ret) {
		DBG(COUT<<env.to_print());
		for( size_t i =0 ; i <rp.r.size(); i ++)
		DBG(COUT<<(rp.r[i].get_context().get()?rp.r[i].get_context().get()->to_print():""));
	}
	return ret;
}

bool typemanager::tcheck(const raw_term &rt) {
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
								if( (uint64_t) rt.e[argc].num > maxval || typexp.pty.get_maxbits() < (int_t)typexp.pty.get_bitsz())
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
			DBG(ss<< "Type signature for predicate "<<rt<< " not found ";);
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

bool typemanager::tcheck(const raw_form_tree &rft) {

	bool ret = true;
	if( rft.type == elem::NONE && !(ret = tcheck(*rft.rt )))
		this->verrs.push_back(tstat);

	if(rft.l != nullptr ) ret &= tcheck(*rft.l);
	if(rft.r != nullptr ) ret &= tcheck(*rft.r);

	return ret;

}

bool typemanager::tcheck(const raw_rule &rr) {
	std::stringstream ss;
	env.reset_context();
	if( rr.get_context().get() != nullptr)
		env.get_context() = *(rr.get_context().get());
	verrs.clear();
	for (const raw_term &ht : rr.h)
		if(!tcheck(ht)) verrs.push_back(tstat);

	if(rr.is_form()) tcheck(*rr.prft);
	else {
		for (auto &it : rr.b)
			for (const raw_term &bt : it)
				if(! tcheck(bt)) verrs.push_back(tstat);
	}
	// update newly discovered var context for rule only if no static type errors
	if (std::count(verrs.begin(), verrs.end(), TINFO_TYPE_CHECK_FAIL ) == 0)
		return rr.update_context(std::make_shared<context>(env.get_context())), true;

	return false;

}

//-----------------------------------------------------------------------------

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
						else if( this->contains_typedef_var(str)) ;
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

} // idni namespace
