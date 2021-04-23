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

bit_elem::bit_elem(const elem &_e, size_t _bsz, bit_term &_pbt): e(_e), bsz(_bsz), pbt(_pbt) {
	p.resize(bsz, false);
	
	int_t sval=0;
	if(e.type == elem::SYM) {
		auto &d = pbt.pbr.pbp.bdict;
		sval = d.get_bit_sym(e);
	}
	for (size_t k = 0; k != bsz; ++k) {
		switch(e.type) {
			case elem::NUM : p[pos(k)] = e.num & (1<<k); break;
			case elem::CHR : p[pos(k)] = e.ch & (1<<k); break;
			case elem::SYM : p[pos(k)] = sval & (1<<k); break;
			case elem::VAR : 
			default:  break;
		}
	}
}
size_t bit_elem::pos(size_t bit_from_right /*, size_t arg, size_t args */) const {
	DBG(assert(bit_from_right < bsz /*&& arg < args*/); )
	return (bsz - bit_from_right - 1); //* args + arg;

	/*
	size_t pos(size_t bit_from_right, size_t arg, size_t args) const {
		DBG(assert(bit_from_right < bits && arg < args);)
		return (bits - bit_from_right - 1) * args + arg;
	}
	*/
}
bool bit_elem::to_elem(std::vector<elem> &ve) const{
	bool ret = true;
	
	if(e.type == elem::VAR || e.type == elem::SYM) {
		for(size_t i=0; i< this->p.size(); i++ ){
			string_t *temp = new string_t( lexeme2str(e.e));
			temp->append( to_string_t((int_t)i));
			lexeme l ={temp->c_str(), temp->c_str()+temp->size()};
			ve.emplace_back(e.type, l);
		}
	}
	else if(e.type == elem::NUM || e.type == elem::CHR) {
		for(bool b: this->p)
			ve.emplace_back(b);
	}
	else ve.emplace_back(e);
	
	return ret;
}
void bit_elem::to_print() const {
	o::dbg()<<e<<" ";
	int i=0;
	for (bool bit : p)
		if(e.type != elem::VAR)
			o::dbg() << (bit ? 1 : 0); 
		else o::dbg()<<e.e<< i++;
}


bit_prog::bit_prog( const raw_prog& _rp ): rp(_rp)  {
	for( const raw_rule &rr :rp.r )
		vbr.emplace_back(bit_rule(rr, *this));
	for( const raw_prog &rp: _rp.nps)
		nbp.emplace_back(bit_prog(rp));
}

bool bit_prog::to_raw_prog(raw_prog &rp) const{
	bool ret = true;
	for( const bit_rule& br :vbr)
		rp.r.emplace_back(),
		ret &= br.to_raw_rule(rp.r.back());
	for( const bit_prog& bp : nbp)
		rp.nps.emplace_back(),
		ret &= bp.to_raw_prog(rp.nps.back());
	return ret;
}

bool bit_univ::btransform( const raw_prog& rpin, raw_prog &rpout ){
	bool ret = true;
	//reset to current prog type definitions
	typenv.build_from ( rpin.vts ); 

	for( const raw_rule &rr : rpin.r)
		rpout.r.emplace_back(), ret &= btransform(rr, rpout.r.back());
	for( const raw_prog rp : rpin.nps)
		rpout.nps.emplace_back(), ret &= btransform(rp, rpout.nps.back());	
	return ret;
}

void bit_prog::to_print() const {
	o::dbg()<<std::endl;
	for( const bit_rule& br :vbr)
		br.to_print(), o::dbg()<<std::endl;
	
	for( const bit_prog& bp : nbp)
		o::dbg()<<"{", 
		bp.to_print(),
		o::dbg()<<"}";
	return;
}


bit_rule::bit_rule(const raw_rule &_rr, bit_prog &_pbp): rr(_rr), pbp(_pbp) {
	for( const raw_term &rt: rr.h)
		bh.emplace_back(bit_term(rt, *this)); 
	for( size_t i=0 ; i < rr.b.size() ; i++) {
		bb.emplace_back();
		for( const raw_term &rt: rr.b[i]) 
			bb.back().emplace_back(bit_term(rt, *this));
	}
}
bool bit_rule::to_raw_rule(raw_rule &rr) const{
	bool ret = true;
	
	for( const bit_term& bt: bh )
		rr.h.emplace_back(),
		ret &= bt.to_raw_term(rr.h.back());
	for( size_t i=0 ; i < bb.size() ; i++) {
		rr.b.emplace_back();
		for( const bit_term &bt: bb[i]) 
			rr.b.back().emplace_back(),
			ret &= bt.to_raw_term(rr.b.back().back());
	}
	
	return ret;

}

bool bit_univ::btransform( const raw_rule& rrin, raw_rule &rrout ){
	bool ret = true;
	for( const raw_term &rt : rrin.h )
		rrout.h.emplace_back(), ret &= btransform(rt, rrout.h.back());
	for( const auto &vrt : rrin.b) {
		rrout.b.emplace_back();
		for( const raw_term &rt : vrt)
			rrout.b.back().emplace_back(), 
			ret &= btransform(rt, rrout.b.back().back());	
	}
	return ret;
}
void bit_rule::to_print() const {
	for( const bit_term& bt: bh )
		bt.to_print(), o::dbg()<< " " ;
	o::dbg()<< (bb.size()? ":-" : ".");
	for( size_t i=0 ; i < bb.size() ; i++)
		for( const bit_term &bt: bb[i]) 
			bt.to_print(), o::dbg()<<" ";
	o::dbg()<<std::endl;
}

bit_term::bit_term(const raw_term &_rt,  bit_rule &_pbr): rt(_rt), pbr(_pbr){	
	for(size_t n= 0 ;n < rt.e.size(); n++ ) {
		int_t bsz ;
		const elem& e = rt.e[n];
		bsz = get_typeinfo(n, rt);
		vbelem.emplace_back(bit_elem(e, bsz, *this));
	}
}
size_t bit_term::get_typeinfo(size_t n, const raw_term &rt){
	for( auto it : pbr.pbp.rp.vts)
		if( it.reln == rt.e[0]){
			if(n>1 && n < rt.e.size()-1) {
				if( it.typeargs[n-2].pty.ty != primtype::NOP)
					return it.typeargs[n-2].pty.get_bitsz();
				else {// struct
					for( auto rit : pbr.pbp.rp.vts)
						if( rit.rty.structname == it.typeargs[n-2].structname ){
							return rit.rty.get_bitsz( pbr.pbp.rp.vts );
						}
					o::err()<< "No type found : "<<it.typeargs[n-2].structname<<std::endl;
					return 0;
				}	
			}
			else if ( n == 0 ) {
				//for now, all predicate are 5 bit in bit_prog
				//to change.
				return 5;
			}
			else  {// for everthing else e.g. paranthesis
				return 0;
			}
		}

	//when types are not specified, default to 4
	if(	rt.e[n].type == elem::SYM || rt.e[n].type == elem::CHR || 
		rt.e[n].type == elem::VAR || rt.e[n].type == elem::NUM )
		return 4;
	else return 0; 
}

bool bit_term::to_raw_term( raw_term& brt ) const {
	bool ret = true;

	brt.neg = rt.neg;
	int_t i = 0;
	for (const bit_elem& be : vbelem) {
			// for predicate rel name
			if( i++ == 0) brt.e.emplace_back(rt.e[0]);
			// for others
			else ret &= be.to_elem(brt.e);
	}
	ret &= brt.calc_arity(0);	
	return ret;
}

size_t bit_univ::get_typeinfo(size_t n, const raw_term &rt) {
	
	string_t reln = lexeme2str(rt.e[0].e);
	if( typenv.contains_pred(reln)) {
		auto targs = typenv.lookup_pred(reln);	
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
		//for anything other than args.
		// TODO:what about +/-* operators as args.
		return 0;
	}
	else {
		//when types are not specified, go default 
		if(	rt.e[n].type == elem::SYM || rt.e[n].type == elem::CHR || 
			rt.e[n].type == elem::VAR || rt.e[n].type == elem::NUM )
			return INT_BSZ;
		return 0;
	}
}

bool bit_univ::btransform(const raw_term& rtin, raw_term& rtout){
	bool ret = true;
	rtout.neg = rtin.neg;
	for(size_t n= 0 ;n < rtin.e.size(); n++ ) {
		const elem& e = rtin.e[n];
		// for predicate rel name, keep as it is
		if( n == 0 ) { rtout.e.emplace_back(e); continue; }
		// get bit size of the given elem and convert to bit representation
		size_t bsz = get_typeinfo(n, rtin);
		if( bsz <=0 || elem::STR == e.type ) { rtout.e.emplace_back(e); continue; }
		std::vector<elem> bitelem(bsz);
		for (size_t k = 0; k != bsz; ++k) {
			switch(e.type) {
				case elem::NUM: bitelem[pos(bsz, k)] = bool(e.num & (1<<k)); break;
				case elem::CHR: bitelem[pos(bsz, k)] = bool(e.ch & (1<<k)); break;
				case elem::VAR:
				case elem::SYM: { string_t temp = lexeme2str(e.e);
								// making new bit sym/vars and avoiding conflict 
								temp.append(to_string_t("_").append(to_string_t((int_t)k)));
								bitelem[pos(bsz, k)] = {e.type, d.get_lexeme(temp)};
								break; }
				default: DBG( COUT<<e<<std::endl; assert(false)); break;
			}
		}
		rtout.e.insert(rtout.e.end(), bitelem.begin(), bitelem.end());
	}
	ret &= rtout.calc_arity(0);
	return ret;
}

void bit_term::to_print() const {
	if ( rt.neg ) COUT<<"~";
	for (const bit_elem& be : vbelem)
		be.to_print(), o::dbg()<<" ";
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
	else if ( !notparam ) return true; // for void parameters in record declarattion

	FAIL:
	in->parse_error(l[pos][0], "Incorrect var declared ", l[pos]);
	return pos = curr, false;
}

bool typestmt::parse( input* in , const raw_prog& prog){
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;
	if( (l[pos][1]-l[pos][0]) == 6 && strncmp(l[pos][0],"record", 6) == 0 ) {
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
				return type_error(" Predicate redefined.", it.reln.e), false;
			predtype.insert({ lexeme2str(it.reln.e), it.typeargs  });		
		}
		else if( it.is_typedef()) { // this is new type definitinon
			if( usertypedef.find(lexeme2str(it.rty.structname.e)) != usertypedef.end() )
				return type_error(" Repeated typedef.", it.rty.structname.e), false;
			usertypedef.insert( { lexeme2str(it.rty.structname.e), it.rty });					}
	}
	return true;
}

bool typechecker::tcheck( const raw_prog &rp){
	bool ret = true;
	for (auto rr : rp.r)
		 ret &= tcheck(rr) ;
	for( auto nrp: rp.nps){
		typechecker tc(nrp);
		ret &= tc.tcheck(nrp) ;
	}
	return ret;
}

bool typechecker::tcheck( const raw_term &rt){
	
	if( env.contains_pred(lexeme2str(rt.e[0].e))){	
		std::stringstream ss;
		auto typeparams = env.lookup_pred(lexeme2str(rt.e[0].e));
		if( typeparams.size() != size_t(rt.arity[0])) 
			return 	ss<<"Expected arity for " << rt << " is " <<typeparams.size(),
					type_error(ss.str().c_str(), rt.e[0].e), false;
		
		size_t argc = 2;
		for( auto typexp: typeparams) {
			if( typexp.is_primitive() ) {
				switch ( rt.e[argc].type) {
					case elem::NUM: 
						if( typexp.pty.ty != primtype::_ptype::UINT)  
						 	return 	ss<<"Expected type for argument "<<argc -1<<":" << rt.e[argc].num << " is ",
							 		ss << typexp.pty.to_print() <<" in predicate "<<rt,
							 		type_error(ss.str().c_str(), rt.e[argc].e), false;
						else if(rt.e[argc].num > ( (0x1 <<typexp.pty.get_bitsz())-1) )
							return 	ss<< rt.e[argc].num << " exceeds max size for ",
							 		ss << typexp.pty.to_print() <<" in predicate "<<rt,
							 		type_error(ss.str().c_str(), rt.e[argc].e), false;	
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

				if(!env.contains_typedef(lexeme2str(typexp.structname.e)))
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
				else env.addtocontext(var, lexeme2str(typexp.structname.e) );
	
			}
			argc++;
		}
	}
	return true;
}

bool typechecker::tcheck( const raw_rule &rr){
	env.reset_context();
	bool ret = true;
	for (const raw_term &ht : rr.h)
		ret &= tcheck(ht);
	for (auto it : rr.b)
		for (const raw_term &bt : it)
			ret &= tcheck(bt) ;
	
	return ret;
}
