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

	typenv = (const_cast<raw_prog&>(rpin)).get_typenv();
	// set the same environment for the output raw bit prog 
	rpout.set_typenv(typenv);
	rpout.g = rpin.g;

	for( const raw_rule &rr : rpin.r)
		rpout.r.emplace_back(), ret &= btransform(rr, rpout.r.back());
	for( const raw_prog &rp : rpin.nps)
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
		rrout.h.emplace_back(), ret &= btransform(rt, rrout.h.back(), rrin, rrout);
	for( const auto &vrt : rrin.b) {
		rrout.b.emplace_back();
		for( const raw_term &rt : vrt)
			rrout.b.back().emplace_back(), 
			ret &= btransform(rt, rrout.b.back().back(), rrin, rrout);	
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

size_t bit_univ::get_typeinfo(size_t n, const raw_term &rt, const raw_rule &rr) {
	
	DBG(assert(rt.e.size()>n && n >=0));

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
	else if( rt.extype == raw_term::REL) {
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

bool bit_univ::btransform(const raw_term& rtin, raw_term& rtout, const raw_rule &rr, raw_rule &rrout){
	bool ret = true;
	rtout.neg = rtin.neg;	
	if( rtin.extype == raw_term::REL) {
		for(size_t n= 0 ;n < rtin.e.size(); n++ ) {
			const elem& e = rtin.e[n];
				// for predicate rel name, keep as it is
				if( n == 0 ) { rtout.e.emplace_back(e); continue; }
				// get bit size of the given elem and convert to bit representation
				size_t bsz = get_typeinfo(n, rtin, rr);
				if( bsz <=0 ) { rtout.e.emplace_back(e); continue; }
				std::vector<elem> bitelem(bsz);
				int_t symbval = 0;
				for (size_t k = 0; k != bsz; ++k) {
					switch(e.type) {
						case elem::NUM: bitelem[pos(bsz, k)] = bool(e.num & (1<<k)); break;
						case elem::CHR: bitelem[pos(bsz, k)] = bool(e.ch & (1<<k)); break;
						case elem::VAR: { 
							string_t temp = lexeme2str(e.e);
							// making new bit vars and avoiding conflict 
							temp.append(to_string_t("_").append(to_string_t((int_t)k)));
							bitelem[pos(bsz, k)] = {elem::VAR, d.get_lexeme(temp)};
							break; 
						}
						case elem::STR:
						case elem::SYM: {
							if( k == 0 ) symbval = d.get_sym(e.e);
							bitelem[pos(bsz, k)] = bool(symbval & (1<<k)); 
							break;
						}
						default: DBG( COUT<<e<<std::endl; assert(false)); break;
					}
				}
				rtout.e.insert(rtout.e.end(), bitelem.begin(), bitelem.end());	
		}
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
									vbit.back()[pos(bsz, k)] = {elem::VAR, d.get_lexeme(temp)};
								}
								break;
				case elem::NUM:
								vbit.emplace_back(); 
								vbit.back().resize(bsz);
								for( size_t k= 0; k !=bsz ; k++)
									vbit.back()[pos(bsz, k)] = bool(e.num & (1<<k));
								break;
				case elem::ARITH:
				case elem::EQ:
				case elem::LEQ: // user size of prev var
								bsz = vbit.back().size();
								vbit.emplace_back(); 
								vbit.back().resize(bsz);
								for( size_t k= 0; k !=bsz ; k++)
									vbit.back()[pos(bsz, k)] = e;
								
								break;
				default : DBG(assert(false));
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
	return true;
}
// infers from given predicates the type signature of relation while
// making use of var context and updates only the pred_type of env.
// returns true if new signature found. Does not update context of vars
// for arith terms, just ensures that all vars have types and returns true	std::vector<typedecl> targs;
// option to change return val; (1) either on new signature, or (2) if everything inferrable.
// currently (2)

bool environment::build_from( const raw_term &rt, bool infer=false){
	string_t str = lexeme2str(rt.e[0].e);

	if( this->contains_pred(str)) return false; 
	std::vector<typedecl> targs;
	size_t st=0, end=rt.e.size();
	bool bknown = true;  // assume all args types are determinable 
	if(rt.extype == raw_term::REL) st = 2, end = rt.e.size()-1;
	for( size_t i= st ; bknown && i < end; i++) {
		str = lexeme2str(rt.e[i].e);
		if(rt.extype == raw_term::REL) {
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
		else DBG(assert(false));
	}

	if(bknown){
			//only insert signature for relations.
			if( rt.extype == raw_term::REL)
		 		str = lexeme2str(rt.e[0].e),
				predtype.insert( { lexeme2str(rt.e[0].e), targs } ).second;
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
			for( size_t i=0; i < rt.e.size(); i++ )
				if(rt.e[i].type== elem::VAR ) {
					str = lexeme2str(rt.e[i].e);
						if (this->contains_prim_var(str) && !lastb)
							lastp = this->lookup_prim_var(str), lastb =true;
						else if( this->contains_typedef_var(str)) ;//TOD): ;
						else notypv.push_back(str);
			}
			for(string_t var: notypv)
				this->addtocontext(var, lastp);
			bknown = lastb;
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
	env.get_context() = *(rr.get_context().get());
	for (const raw_term &ht : rr.h){
		string_t str = lexeme2str(ht.e[0].e);
		if(env.contains_pred(str)) continue;
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
			if(env.contains_pred(str)) continue;
			if(!env.build_from(bt, infer) ){
				ss<<"Could not infer types from predicate "<<bt,
				type_error(ss.str().c_str(), bt.e[0].e );
				ss.str("");
				ss.clear();
			}
			else ret = true;
		}

	if(ret) *(rr.get_context().get()) = env.get_context();
	return ret;
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
		else ret = false, infer = false, vrinfo[i] = TINFO_TYPE_CHECK_FAIL; // type_check fails.
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
				else ret =false, infer=false, vrinfo[i] = TINFO_TYPE_CHECK_FAIL;
			}
		}
		if(lastinfo != vrinfo) { goto _BEG; }
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
	return ret;
}

bool typechecker::tcheck( const raw_term &rt){
	tstat = TINFO_TYPE_CHECK_SUCCESS;
	string_t str = lexeme2str(rt.e[0].e);

	std::stringstream ss;
	if( rt.extype == raw_term::REL ) {
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
								int_t maxval =  ( ((size_t)0x1 <<typexp.pty.get_bitsz())-1);
								if( rt.e[argc].num > maxval )
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
					
					if( rt.extype == raw_term::ARITH && lastp.ty != primtype::_ptype::UINT )
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
		/*
	if(tryinfer) {
		// for inference, use prev context for terms whose types are not known yet
		env.get_context() = *(rr.get_context().get());
		for (const raw_term &ht : rr.h){
			string_t str = lexeme2str(ht.e[0].e);
			if(env.contains_pred(str)) continue;
			if(!env.build_from(ht, infer) ){
				ret &= false;
				ss<<"Could not infer types from"<<ht,
				type_error(ss.str().c_str(), ht.e[0].e );
				ss.str("");
				ss.clear();
			}
			else rr.update_context(std::make_shared<context>(env.get_context()));
		}
		for (auto &it : rr.b)
			for (const raw_term &bt : it) {
				string_t str = lexeme2str(bt.e[0].e);
				if(env.contains_pred(str)) continue;
				if(!env.build_from(bt, infer) ){
					ret &= false;
					ss<<"Could not infer types from predicate "<<bt,
					type_error(ss.str().c_str(), bt.e[0].e );
					ss.str("");
					ss.clear();
				}
				else rr.update_context(std::make_shared<context>(env.get_context()));
			}
		return ret;
	}
 */
}
