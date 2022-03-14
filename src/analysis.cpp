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

	ptypenv = (const_cast<raw_prog&>(rpin)).typenv;
	// set the same environment for the output raw bit prog 
	rpout.g = rpin.g;

	for( const raw_rule &rr : rpin.r)
		rpout.r.emplace_back(), ret &= btransform(rr, rpout.r.back());
	#ifdef BIT_TRANSFORM
	for( const raw_prog &rp : rpin.nps)
		rpout.nps.emplace_back(d), ret &= btransform(rp, rpout.nps.back());
	#endif
	return ret;
}

bool bit_univ::btransform( const raw_form_tree& rfin, raw_form_tree &rfout, const raw_rule& rrin, raw_rule &rrout ) {
	
	bool ret= true;
	if(rfin.type == elem::NONE)
	 	(*rfout.rt).clear(), ret &= btransform(*rfin.rt, *rfout.rt, rrin, rrout );
	if(rfin.l != nullptr) ret &= btransform(*rfin.l, *rfout.l, rrin, rrout );
	if(rfin.r != nullptr) ret &= btransform(*rfin.r, *rfout.r, rrin, rrout );
	return ret;
}

bool bit_univ::btransform( const raw_rule& rrin, raw_rule &rrout ){
	bool ret = true;
	for( const raw_term &rt : rrin.h )
		rrout.h.emplace_back(), ret &= btransform(rt, rrout.h.back(), rrin, rrout);		
	if( rrin.is_form())	{
		//*rrout.prft = *rrin.prft,
		rrout.set_prft(*rrin.prft);
		ret = btransform( *rrin.prft, *rrout.prft, rrin, rrout  );
		DBG((*rrout.prft).printTree();)
	} else {
		for( const auto &vrt : rrin.b) {
			rrout.b.emplace_back();
			for( const raw_term &rt : vrt)
				rrout.b.back().emplace_back(), 
				ret &= btransform(rt, rrout.b.back().back(), rrin, rrout);	
		}
	}
	return ret;
}

const primtype& bit_univ::get_typeinfo(size_t n, const raw_term &rt, const raw_rule &rr) {
	
	DBG(assert(rt.e.size()>n && (int_t)n >=0 && rr.varctx.get()) );

	if(rt.extype == raw_term::ARITH || rt.extype == raw_term::EQ || rt.extype == raw_term::LEQ) {
		string_t str = lexeme2str(rt.e[n].e);
		if( rt.e[n].type == elem::VAR ) {
			if( rr.varctx.get()->contains_prim_var(str) )
				return rr.varctx.get()->lookup_prim_var(str);
			else if( rr.varctx.get()->contains_typedef_var(str) ) {
				//todo for struct types.
				//should struct types ever have arithmetic operation, no!
				DBG(assert(false));
				//return this->ptypenv->lookup_typedef_var(str);
				return dt_nop;
			}
			else {
				//should this case ever happen when ctx does not know the type of var? no.
				// typecheck should have failed before.
				DBG(assert(false));
				return dt_nop;
			}
		}
		else if ( rt.e[n].type == elem::NUM ) { 
			// get the type info based on nearest var
			int_t  ni = n, args = rt.e.size();
			for ( int_t i = n; i>=0 && i < args ; i++ )
				if ((rt.e[ni = i].type == elem::VAR) || (rt.e[ni = args-i-1].type == elem::VAR))
					break;
			DBG(assert(ni!=( int_t)n));

			if (ni>=0 && ni < args)
				return get_typeinfo(ni, rt, rr);
		
			return dt_int;
		}
	}
	else if( rt.extype == raw_term::REL || rt.extype == raw_term::BLTIN) {
		string_t reln = lexeme2str(rt.e[0].e);
		if( ptypenv->contains_pred(reln)) {
			auto &targs = ptypenv->lookup_pred(reln);
			//only for arguments
			if(n>1 && n < rt.e.size()-1) {
				if(targs[n-2].is_primitive())
					return targs[n-2].pty;
				else {
					DBG(assert(targs[n-2].is_usertype()));
					string_t stn = lexeme2str(targs[n-2].structname.e);
					if(ptypenv->contains_typedef( stn)){
						return dt_nop; 
						// not supported
						//return ptypenv->lookup_typedef(stn);
						
					}
					o::err()<< "No type found : "<<targs[n-2].structname<<std::endl;
				}
			} 
			
		}
		else {
			//when types are not specified, go default
			// should we ever reach this case? NO
			DBG(assert(false));
			if(	rt.e[n].type == elem::SYM || rt.e[n].type == elem::CHR || 
				rt.e[n].type == elem::VAR || rt.e[n].type == elem::NUM )
				return dt_int;
		}
	}
	// for everything else
	return dt_nop;
}
bool bit_univ::brev_transform_check(const term &t, const table &tab){

	string_t pred = lexeme2str(d.get_rel(tab.s.first));
	bool found =false;
	const std::vector<typedecl> &vt = this->ptypenv->search_pred(pred, found, t.size());
	if(found == false){
		DBG(assert(false));
		return false;
	}
	tab_args tabarg;
	for(typedecl td: vt ) {
		if( td.is_primitive() )
			tabarg.emplace_back(td.pty.get_bitsz());
		else tabarg.emplace_back(); //handle later
	}
	//auto rtab = rtabs.find(pred)->second;
	int_t val = 0;
	//for symbols, check if the value is in dict
	for( int_t arg=0; arg < (int_t)vt.size(); arg++)
		if( vt[arg].is_primitive() && vt[arg].pty == primtype::SYMB) {
			size_t  bitsz = vt[arg].pty.get_bitsz();
			val = 0;				
			//construct arg value from bits using pos					
			for( size_t k = 0; k < bitsz; k++) {
				int_t ps = pos( bitsz, k, arg, vt.size(), tabarg);
				//DBG(COUT<<ps<<std::endl);	
				DBG(assert(ps < (int_t)t.size()));
				val |= t[ps] << k;
			}
			if(! d.is_valid_sym_val(val)) return false;
		}
		
	return true;
}

//inplace transformation of bit raw term to normal as per type_env/
bool bit_univ::brev_transform( raw_term &rbt ){
	
	string_t str = lexeme2str(rbt.e[0].e);
	bool found = false;
	const std::vector<typedecl> &vt = this->ptypenv->search_pred(str, found, rbt.get_formal_arity());
	if(found == false ) return false;
	//auto rtab = this->rtabs.find(str)->second;
	int_t bitsz = -1;
	int_t val = 0, arg = 0,  args = vt.size();
	// save bits and clear from rbt
	std::vector<elem> rbits{ rbt.e.begin()+2, rbt.e.end()-1 };
	rbt.e.erase(rbt.e.begin()+2, rbt.e.end()-1);

	tab_args tabarg;
	for(typedecl td: vt ) {
		if( td.is_primitive() )
			tabarg.emplace_back(td.pty.get_bitsz());
		else tabarg.emplace_back(); //handle later
	}

	for(typedecl td: vt ) {
		if( td.is_primitive() ) {
			bitsz =  td.pty.get_bitsz();
			val = 0;				
			//construct arg value from bits using pos					
			for( int_t k = 0; k < bitsz; k++) {
				int_t ps = pos( bitsz, k, arg, args, tabarg);
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

void bit_univ::append_types( string_t &name, std::vector<primtype>& ty) {
	for_each( ty.begin(), ty.end(), 
		[&name](primtype &pt) {
			 name.append(to_string_t(pt.to_print()));
	 });
}
std::vector<primtype> bit_univ::get_arg_types( const raw_term & rt, const raw_rule & rr){
	std::vector<primtype> vty;
	size_t st = 0, end = rt.e.size();
	if(rt.extype == raw_term::REL || rt.extype == raw_term::BLTIN )
		st=2, end--;
	for( ; st < end ; st++){
		const primtype& pt = get_typeinfo(st, rt, rr);
		if(end != rt.e.size() || pt.ty != primtype::NOP )  
			vty.emplace_back(pt);
	}
	return vty;
}
bool bit_univ::btransform(const raw_term& rtin, raw_term& rtout, const raw_rule &rr, raw_rule &rrout){
	bool ret = true;
	rtout.neg = rtin.neg;	
	//getting types for args 
	std::vector<primtype> types = get_arg_types(rtin, rr);
	// getting total bits for args table/predicate
	size_t totalsz = 0;
	tab_args targs;
	for( primtype& atp : types )
		 targs.emplace_back(atp.get_bitsz()), totalsz +=  targs.back();

	if( rtin.extype == raw_term::REL || rtin.extype == raw_term::BLTIN) {	
		int_t args = rtin.e.size() == 1 ? 0: rtin.e.size()-3;	
		DBG(assert(args == rtin.arity[0]));

		// fill table arg size. better to have a separate function.
		/*
		for(typedecl td: predtype ) {
			if( td.is_primitive() )
				targs.emplace_back(td.pty.get_bitsz());
			else {
				string_t st = lexeme2str(td.structname.e);
				targs.emplace_back(ptypenv->lookup_typedef(st).get_bitsz(*ptypenv));
			}
		}
		*/
		std::vector<elem> bitelem(totalsz);
		DBG(COUT<<"size for "<<rtin.e[0].e<< "="<<totalsz<<std::endl);
		for(size_t n= 0 ;n < rtin.e.size(); n++ ) {
			const elem& e = rtin.e[n];
			// for predicate rel name and (), keep as it is
			if( n <= 1 || n == rtin.e.size()-1 ) { rtout.e.emplace_back(e); continue; }		
			// get bit size of the given elem and convert to bit representation/
			size_t bsz = types[n-2].get_bitsz();
			int_t symbval = 0;
			for (size_t k = 0; k != bsz; ++k) {
				
				int_t ps = pos(bsz, k, n-2, args, targs);
			//	DBG(COUT<< ps<<std::endl;assert(ps < bitelem.size()));
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
		}
		//insert before last enclosing paranthesis
		if(bitelem.size()) rtout.e.insert(rtout.e.end()-1, bitelem.begin(), bitelem.end());
		ret &= rtout.calc_arity(0);
	}
	else if ( rtin.extype == raw_term::ARITH || rtin.extype == raw_term::EQ || rtin.extype == raw_term::LEQ) {
		
		// prepare tab_arg and estimate size of bit elements from the context of the rule, since 
		// these are arithmetic variables having no specific type signture, but only the context contains
		// such bitsizes as calculated during typeinference.
		/*
		tab_args tag;
		int_t tsz = 0;
		for(size_t n = 0 ; n < rtin.e.size(); n++ ) {
			size_t bsz = get_typeinfo(n, rtin, rr);
			if(bsz) tag.push_back(bsz), tsz += bsz;
		}
		*/
		//DBG(assert(tag.size() == (size_t)rtin.get_formal_arity()-2));
		size_t  args = targs.size();
		std::vector<elem> vbit(totalsz);
		// for gettin operator index
		string_t bitrelname[2];
		size_t opi = 0; 
		for(size_t bsz, arg = 0, n = 0 ; n < rtin.e.size(); n++ ) {
			if(n && !(n == 1 || n == 3) ) arg++;  // skip operators in arith or eq term
			const elem& e = rtin.e[n];
			string_t str = lexeme2str(e.e);
			switch( e.type ){
				case elem::VAR: 
								bsz = targs[arg];
								for( size_t k= 0; k !=bsz ; k++){
									size_t ps = pos(bsz, k, arg, args, targs );
									string_t temp = str;
									temp.append(to_string_t("_").append(to_string_t((int_t)k)));
									vbit[ps] = {elem::VAR, d.get_lexeme(temp)};
								}
								break;
				case elem::NUM:
								bsz = targs[arg];
								for( size_t k= 0; k !=bsz ; k++)
									vbit[pos(bsz, k, arg, args, targs)] = bool(e.num & (1<<k));
								break;
				case elem::ARITH: 
						switch(e.arith_op){

							case t_arith_op::ADD : bitrelname[opi++] = to_string_t("_PLUS_"); break; 
							case t_arith_op::BITWAND: bitrelname[opi++] = to_string_t("_BAND_");break;
							case t_arith_op::BITWOR: bitrelname[opi++] = to_string_t("_BOR_");break;
							case t_arith_op::BITWNOT: bitrelname[opi++] = to_string_t("_BNOT_");break;
							case t_arith_op::BITWXOR: bitrelname[opi++] = to_string_t("_BXOR_");break;
							case t_arith_op::MULT: bitrelname[opi++] = to_string_t("_MULT_");break;
							case t_arith_op::SHL: bitrelname[opi++] = to_string_t("_SHL_");break;
							case t_arith_op::SHR: bitrelname[opi++] = to_string_t("_SHR_");break;
							case t_arith_op::SUB: bitrelname[opi++] = to_string_t("_SUB_");break;
							default: DBG(COUT<<rtin<<std::endl); assert(false); 
						}
					break;
				
				case elem::EQ: bitrelname[opi++] = to_string_t("_EQ_") ; break;
				case elem::LEQ: bitrelname[opi++] = to_string_t("_LEQ_"); break;
				case elem::NEQ:bitrelname[opi++] = to_string_t("_EQ_"); break;
				case elem::GEQ:bitrelname[opi++] = to_string_t ("_LEQ_"); break;
				case elem::LT:bitrelname[opi++] = to_string_t("_LT_"); break;
				case elem::GT:bitrelname[opi++] = to_string_t("_LT_"); break;
				default : DBG(COUT<<rtin<<std::endl); assert(false);
			}
		}
		
		//change to relation in order to emit for binary comparisons
		// e.g  _LEQ_(--  -- ) a != b  ----> neq( a  b)
		//change to REL and add new relation in order
		// to emit for ternary arith e.g. _plus_( 11 1 1  000  ?z0?z1?z2 ),
		// a + 1 < b  ---->   plus(a 1,z ) , lt ( z , b)
		// oprd1 operator oprd2 comp_operator oprd3
		rtout.extype = raw_term::REL;
		append_types( bitrelname[0] , types);
		ptypenv->add_sig(bitrelname[0], types);
		rtout.e.emplace_back(elem(elem::SYM, d.get_lexeme(bitrelname[0])) ); // from first operator
		rtout.e.emplace_back(elem(elem::OPENP));
		rtout.e.insert(rtout.e.end(), vbit.begin(), vbit.end() );
		rtout.e.emplace_back(elem(elem::CLOSEP));
		ret = rtout.calc_arity(nullptr);

		if( rtin.extype == raw_term::ARITH && rtin.e[3].type != elem::EQ )  { // when com_operator != =
			// now we need to replace oprnd3's bit with tmp var z in vbit
			// reprsenting ternary arith
			// and put oprnd3's in the new relation along with tmp
			size_t bsz = targs[2];  // oprnd3 size   
			std::vector<primtype> types2 { types[2], types[2]};
			tab_args tag2{targs[2], targs[2]}; // for tmp z and oprd3
			// size of tmp z and oprd3 
			std::vector<elem> vbit2(tag2[0] + targs[1]);
			string_t temp = lexeme2str(rtin.e[rtin.e.size()-1].e);
			DBG(assert((args-1) == tag2.size()));
			for( size_t k= 0; k != bsz ; k++){
				//getting prev pos of oprnd3
				size_t ps = pos(bsz, k, 2, args, targs );
				//constructing new tmp var
				temp.append(to_string_t("_tmp_").append(to_string_t((int_t)k)));
				// get pos of oprnd3 in new relation and place it
				size_t ps2 = pos(bsz, k, 1, tag2.size(), tag2 );
				vbit2[ps2] = vbit[ps];
				// get pos of tmp in new rateion and place it
				ps2 = pos(bsz, k , 0, tag2.size(), tag2);
				vbit2[ps2] = {elem::VAR, d.get_lexeme(temp)};
				// put new tmp vaz z in ternay relation old
				vbit[ps] = vbit[ps2]; 
			}
			// preparing new raw_term for the new relation.
			raw_term frt;
			frt.extype = raw_term::REL;
			append_types(bitrelname[1],types2);
			ptypenv->add_sig(bitrelname[1], types2);
			// from comp_operator
			frt.e.emplace_back(elem(elem::SYM, d.get_lexeme(bitrelname[1]))); 
			frt.e.emplace_back(elem(elem::OPENP));
			frt.e.insert(frt.e.end(),vbit2.begin(), vbit2.end());
			frt.e.emplace_back(elem(elem::CLOSEP));
			ret &= frt.calc_arity(nullptr);
			// don't forget to add this new term to body
			rrout.b.back().push_back(frt);
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

bool typechecker::tinfer( const raw_form_tree &rft){
	
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

	for( auto &nrp: rp.nps){
		nrp.typenv->set_parent(rp.typenv);
		typechecker tc(nrp, infer);
		ret &= tc.tcheck() ;
		rp.typenv->set_nested(nrp.typenv);
	}
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

bool typechecker::tcheck(const raw_form_tree &rft){

	bool ret = true;
	if( rft.type == elem::NONE && !(ret = tcheck(*rft.rt ))) 
		this->verrs.push_back(tstat);

	if(rft.l != nullptr ) ret &= tcheck(*rft.l);
	if(rft.r != nullptr ) ret &= tcheck(*rft.r);

	return ret;

}
bool typechecker::tcheck( const raw_rule &rr){
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
