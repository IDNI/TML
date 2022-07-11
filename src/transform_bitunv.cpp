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


#include "ir_builder.h"
#include "tables.h"

#ifdef BIT_TRANSFORM

bool ir_builder::btransform(raw_prog& rpin) {
	bool ret = true;
	std::vector<raw_rule> r;
	for( const raw_rule &rr : rpin.r)
		r.emplace_back(), ret &= btransform(rr, r.back());
	rpin.r.clear();
	rpin.r = r;
	//for( const raw_prog &rp : rpin.nps)
	//	rpout.nps.emplace_back(d), ret &= btransform(rp, rpout.nps.back());
	return ret;
}

bool ir_builder::btransform(const raw_form_tree& rfin, raw_form_tree &rfout,
		const raw_rule& rrin, raw_rule &rrout) {
	bool ret= true;
	if(rfin.type == elem::NONE)
	 	(*rfout.rt).clear(), ret &= btransform(*rfin.rt, *rfout.rt, rrin, rrout );
	if(rfin.l) ret &= btransform(*rfin.l, *rfout.l, rrin, rrout );
	if(rfin.r) ret &= btransform(*rfin.r, *rfout.r, rrin, rrout );
	return ret;
}

bool ir_builder::btransform(const raw_rule& rrin, raw_rule &rrout) {
	bool ret = true;
	for (const raw_term &rt : rrin.h)
		rrout.h.emplace_back(), ret &= btransform(rt, rrout.h.back(), rrin, rrout);		
	if (rrin.is_form())	{
		//*rrout.prft = *rrin.prft,
		rrout.set_prft(*rrin.prft);
		ret = btransform( *rrin.prft, *rrout.prft, rrin, rrout  );
		DBG((*rrout.prft).printTree();)
	} else {
		for (const auto &vrt : rrin.b) {
			rrout.b.emplace_back();
			for( const raw_term &rt : vrt)
				rrout.b.back().emplace_back(), 
				ret &= btransform(rt, rrout.b.back().back(), rrin, rrout);	
		}
	}
	return ret;
}

const primtype& ir_builder::get_typeinfo(size_t n, const raw_term &rt, const raw_rule &rr) {
	
	DBG(assert(rt.e.size()>n && (int_t)n >=0 && rr.varctx.get()) );

	if (rt.extype == raw_term::ARITH || rt.extype == raw_term::EQ ||
			rt.extype == raw_term::LEQ) {
		string_t str = lexeme2str(rt.e[n].e);
		if (rt.e[n].type == elem::VAR ) {
			if( rr.varctx.get()->contains_prim_var(str) )
				return rr.varctx.get()->lookup_prim_var(str);
			else if( rr.varctx.get()->contains_typedef_var(str) ) {
				//todo for struct types.
				//should struct types ever have arithmetic operation, no!
				DBG(assert(false));
				//return this->env.lookup_typedef_var(str);
				return dt_nop;
			}
			else {
				//should this case ever happen when ctx does not know the type of var? no.
				// typecheck should have failed before.
				DBG(assert(false));
				return dt_nop;
			}
		}
		else if (rt.e[n].type == elem::NUM) {
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
	else if (rt.extype == raw_term::REL || rt.extype == raw_term::BLTIN) {
		string_t reln = lexeme2str(rt.e[0].e);
		if( tc.env.contains_pred(reln)) {
			auto &targs = tc.env.lookup_pred(reln);
			//only for arguments
			if(n>1 && n < rt.e.size()-1) {
				if(targs[n-2].is_primitive())
					return targs[n-2].pty;
				else {
					DBG(assert(targs[n-2].is_usertype()));
					string_t stn = lexeme2str(targs[n-2].structname.e);
					if(tc.env.contains_typedef( stn)){
						return dt_nop; 
						// not supported
						//return env.lookup_typedef(stn);
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

bool ir_builder::brev_transform_check(const term &t, const table &tab) {

	string_t pred = lexeme2str(dict.get_rel_lexeme(tab.s.first));
	bool found = false;
	const std::vector<typedecl> &vt = tc.env.search_pred(pred, found, t.size());
	if(!found){
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
			if(! dict.is_valid_sym_val(val)) return false;
		}
		
	return true;
}

//inplace transformation of bit raw term to normal as per type_env/
bool ir_builder::brev_transform(raw_term &rbt) {
	
	string_t str = lexeme2str(rbt.e[0].e);
	bool found = false;
	const std::vector<typedecl> &vt = tc.env.search_pred(str, found, rbt.get_formal_arity());
	if(found == false ) return false;
	//auto rtab = this->rtabs.find(str)->second;
	int_t bitsz = -1;
	int_t val = 0, arg = 0,  args = vt.size();
	// save bits and clear from rbt
	std::vector<elem> rbits{ rbt.e.begin()+2, rbt.e.end()-1 };
	rbt.e.erase(rbt.e.begin()+2, rbt.e.end()-1);

	tab_args tabarg;
	for (typedecl td: vt) {
		if (td.is_primitive())
			tabarg.emplace_back(td.pty.get_bitsz());
		else tabarg.emplace_back(); //handle later
	}

	for (typedecl td: vt) {
		if (td.is_primitive()) {
			bitsz =  td.pty.get_bitsz();
			val = 0;				
			//construct arg value from bits using pos					
			for( int_t k = 0; k < bitsz; k++) {
				int_t ps = pos( bitsz, k, arg, args, tabarg);
				//DBG(COUT<<ps<<std::endl);	
				val |= rbits[ps].num << k;
			}
			elem el;
			if (td.pty.ty == primtype::UINT)
				el = elem(val);
			else if (td.pty.ty == primtype::UCHAR)
				el = elem((char32_t) val);
			else if (td.pty.ty == primtype::SYMB)   // should differentiate from STR
				el = elem(elem::SYM, this->dict.get_sym_lexeme(val) );

			rbt.e.insert(rbt.e.begin() + 2 + arg, el);
			arg++;
		}
		else { } //structtypes userdef
	}
	return true;
}

void ir_builder::append_types(string_t &name, std::vector<primtype>& ty) {
	for_each( ty.begin(), ty.end(), 
		[&name](primtype &pt) {
			 name.append(to_string_t(pt.to_print()));
	 });
}

std::vector<primtype> ir_builder::get_arg_types(const raw_term & rt, const raw_rule & rr) {
	std::vector<primtype> vty;
	size_t st = 0, end = rt.e.size();
	if (rt.extype == raw_term::REL || rt.extype == raw_term::BLTIN)
		st=2, end--;
	for ( ; st < end ; st++) {
		const primtype& pt = get_typeinfo(st, rt, rr);
		if (end != rt.e.size() || pt.ty != primtype::NOP)
			vty.emplace_back(pt);
	}
	return vty;
}

bool ir_builder::btransform(const raw_term& rtin, raw_term& rtout, const raw_rule &rr,
		raw_rule &rrout) {
	bool ret = true;
	rtout.neg = rtin.neg;	
	//getting types for args 
	std::vector<primtype> types = get_arg_types(rtin, rr);
	// getting total bits for args table/predicate
	size_t totalsz = 0;
	tab_args targs;
	for (primtype& atp : types)
		 targs.emplace_back(atp.get_bitsz()), totalsz +=  targs.back();

	if (rtin.extype == raw_term::REL || rtin.extype == raw_term::BLTIN) {
		int_t args = rtin.e.size() == 1 ? 0: rtin.e.size()-3;	
		DBG(assert(args == rtin.arity[0]));

		// fill table arg size. better to have a separate function.
		/*
		for(typedecl td: predtype ) {
			if( td.is_primitive() )
				targs.emplace_back(td.pty.get_bitsz());
			else {
				string_t st = lexeme2str(td.structname.e);
				targs.emplace_back(env.lookup_typedef(st).get_bitsz(*ptypenv));
			}
		}
		*/
		std::vector<elem> bitelem(totalsz);
		DBG(COUT<<"size for "<<rtin.e[0].e<< "="<<totalsz<<std::endl);
		for (size_t n= 0 ;n < rtin.e.size(); n++) {
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
						bitelem[ps] = {elem::VAR, dict.get_lexeme(temp)};
						break; 
					}
					case elem::STR:
					case elem::SYM: {
						if( k == 0 ) symbval = dict.get_sym(e.e);
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
	else if (rtin.extype == raw_term::ARITH || rtin.extype == raw_term::EQ ||
			rtin.extype == raw_term::LEQ) {
		
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
		for (size_t bsz, arg = 0, n = 0 ; n < rtin.e.size(); n++) {
			if(n && !(n == 1 || n == 3) ) arg++;  // skip operators in arith or eq term
			const elem& e = rtin.e[n];
			string_t str = lexeme2str(e.e);
			switch (e.type) {
				case elem::VAR: 
								bsz = targs[arg];
								for( size_t k= 0; k !=bsz ; k++){
									size_t ps = pos(bsz, k, arg, args, targs );
									string_t temp = str;
									temp.append(to_string_t("_").append(to_string_t((int_t)k)));
									vbit[ps] = {elem::VAR, dict.get_lexeme(temp)};
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
		tc.env.add_sig(bitrelname[0], types);
		rtout.e.emplace_back(elem(elem::SYM, dict.get_lexeme(bitrelname[0])) ); // from first operator
		rtout.e.emplace_back(elem(elem::OPENP));
		rtout.e.insert(rtout.e.end(), vbit.begin(), vbit.end() );
		rtout.e.emplace_back(elem(elem::CLOSEP));
		ret = rtout.calc_arity(nullptr);

		if (rtin.extype == raw_term::ARITH && rtin.e[3].type != elem::EQ) { // when com_operator != =
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
			for (size_t k= 0; k != bsz ; k++) {
				//getting prev pos of oprnd3
				size_t ps = pos(bsz, k, 2, args, targs );
				//constructing new tmp var
				temp.append(to_string_t("_tmp_").append(to_string_t((int_t)k)));
				// get pos of oprnd3 in new relation and place it
				size_t ps2 = pos(bsz, k, 1, tag2.size(), tag2 );
				vbit2[ps2] = vbit[ps];
				// get pos of tmp in new rateion and place it
				ps2 = pos(bsz, k , 0, tag2.size(), tag2);
				vbit2[ps2] = {elem::VAR, dict.get_lexeme(temp)};
				// put new tmp vaz z in ternay relation old
				vbit[ps] = vbit[ps2]; 
			}
			// preparing new raw_term for the new relation.
			raw_term frt;
			frt.extype = raw_term::REL;
			append_types(bitrelname[1],types2);
			tc.env.add_sig(bitrelname[1], types2);
			// from comp_operator
			frt.e.emplace_back(elem(elem::SYM, dict.get_lexeme(bitrelname[1])));
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
#endif
