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
#include "input.h"

bit_elem::bit_elem(const elem &_e, size_t _bsz, bit_term &_pbt): e(_e), bsz(_bsz), pbt(_pbt) {
	p.resize(bsz, false);
	
	int_t sval=0;
	if(e.type == elem::SYM) {
		auto &d = pbt.pbr.pbp.bit_dict;
		if(d.find(e.e) == d.end())
			d.insert({e.e, d.size()+1});
		sval = d[e.e];
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
void bit_elem::to_print() const {
	o::out()<<e<<" ";
	int i=0;
	for (bool bit : p)
		if(e.type != elem::VAR)
			o::out() << (bit ? 1 : 0); 
		else o::out()<<e.e<< i++;
}


bit_prog::bit_prog( const raw_prog& _rp ): rp(_rp)  {
	for( const raw_rule &rr :rp.r )
		vbr.emplace_back(bit_rule(rr, *this));
}

void bit_prog::to_print() const {
	o::out()<<std::endl;
	for( const bit_rule& br :vbr)
		br.to_print(), o::out()<<std::endl;
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
void bit_rule::to_print() const {
	for( const bit_term& bt: bh )
		bt.to_print(), o::out()<< " " ;
	o::out()<< (bb.size()? ":-" : ".");
	for( size_t i=0 ; i < bb.size() ; i++)
		for( const bit_term &bt: bb[i]) 
			bt.to_print(), o::out()<<" ";
	o::out()<<std::endl;
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
					o::err()<< "No struct type found : "<<it.typeargs[n-2].structname<<std::endl;
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

void bit_term::to_print() const {
	for (const bit_elem& be : vbelem)
		be.to_print(), COUT<<" ";
}


size_t structype::get_bitsz(const std::vector<typestmt> &rcdtypes){
	size_t bsz=0;
	static std::set<elem> done;
	if(done.find(structname) != done.end()) { 
		o::dbg()<<"Recursive type "<< structname <<" not defined completely" <<std::endl;
		return bsz;
	}
	done.insert(structname);
				
	for( auto md : this->membdecl) {
			if(md.pty.ty != primtype::NOP) 
				bsz += md.pty.get_bitsz()*md.vars.size();
			else {	// do for record;
				for( auto rit : rcdtypes)
					if( rit.rty.structname == md.structname  )
						bsz +=  rit.rty.get_bitsz( rcdtypes ) * md.vars.size();
			}
		}
	done.erase(this->structname);
	return bsz;
}
bool primtype::parse( input* in , const raw_prog& prog){

	static const std::map<std::string, _ptype> tym = { {"int", UINT},
											{"char", UCHAR},
											{"symb", SYMB}
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

	if( strncmp(l[pos++][0],"struct", 6) ) goto FAIL;
	if( !structname.parse(in) || structname.type != elem::SYM ) goto FAIL;
	if(*l[pos++][0] != '{') goto FAIL;

	while( pos < l.size() &&  *l[pos][0] != '}') {
		membdecl.emplace_back();
		if(false == membdecl.back().parse(in, prog)) {
				in->parse_error(l[pos][0], "Incorrect member declaration", l[pos]);
				goto FAIL;
			}		
	}
	if(*l[pos++][0] == '}') return true;

	FAIL: return pos=curr, false;
}
bool typedecl::parse( input* in , const raw_prog& prog){
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;
	if ( pty.parse(in, prog) || (structname.parse(in) && structname.type == elem::SYM) ) {
		for( ;pos < l.size() ; )  {
			vars.emplace_back();
			if( ! vars.back().parse(in) || vars.back().type != elem::VAR ) goto FAIL;
			if( *l[pos][0] == '.') { pos++; break; }
			else if (*l[pos++][0] != ',') goto FAIL;
		}
		if(vars.size())	return true;
	}
	FAIL:
	in->parse_error(l[pos][0], "Incorrect var declared ", l[pos]);
	return pos = curr, false;
}

bool typestmt::parse( input* in , const raw_prog& prog){
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;
	if( strncmp(l[pos][0],"record", 6) == 0 ) {
		pos++;
		if( !reln.parse(in) || reln.type != elem::SYM ) goto FAIL;
		if(*l[pos++][0] != '{') goto FAIL;
		for( ;pos < l.size() && *l[pos][0] != '}'; ) {
			typeargs.emplace_back();
			if( !typeargs.back().parse(in, prog) ) goto FAIL;
		}
		if(*l[pos++][0] != '}') goto FAIL;
		return true;
	}
	else if ( strncmp(l[pos][0],"struct", 6) == 0  ) {
		if( rty.parse(in, prog)) return true;
	}
	FAIL:
	return pos=curr, false;
}
