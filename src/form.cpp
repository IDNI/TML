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

#include "form.h"
#include "tables.h"
using namespace std;

extern uints perm_init(size_t n);

pnft::pnft(){
		varslen = 0, varslen_h = 0, neg = false, b = 0, cons = bdd_handle::T;
}

pnft::~pnft() {
		if(b) delete b, b = NULL;
		if (auto p = get<1>(hvar_b)) delete p;
}

bool pnft::is_quant(form *f) const {
	//TODO: make ftype a typedef so we can pass type as argument directly
	if ((f->type == form::FORALL1) || (f->type == form::EXISTS1) || (f->type == form::UNIQUE1) ||
		(f->type == form::FORALL2) || (f->type == form::EXISTS2) || (f->type == form::UNIQUE2))
		return true;
	return false;
}

quant_t pnft::to_quant_t(form *f) const {
		quant_t q = EX;
		switch (f->type) {
			case form::FORALL1: q = FA; break;
			case form::EXISTS1: q = EX; break;
			case form::UNIQUE1: q = UN; break;
			case form::FORALL2: q = FAH; break;
			case form::EXISTS2: q = EXH; break;
			case form::UNIQUE2: q = UNH; break;
			default: assert(GET_BDD_ID(F));
		}
		return q;
}
bool pnft::fp(class tables *s) const {

	for (auto b: bodies)
		if (!(b->tlast && b->tlast->b == s->tbls[b->tab].t->b))
			return false;
	return true;
}

void pnft::print() const {
 ;
}

void pnft::quantify(spbdd_handle &q, size_t bits) const {

#ifndef TYPE_RESOLUTION
	size_t bits_l = bits - 2;
#else
	size_t bits_l = bits;
#endif

	//TODO: move perms inits to preparation
	uints perm1 = perm_init((bits_l)*varslen);
	uints perm2 = perm_init((bits_l)*varslen);
	for (size_t i = 0; i < varslen; i++)
		for (size_t j = 0; j < bits_l; j++) {
			perm1[j * varslen + i] = i*(bits_l)+j;
			perm2[i*(bits_l)+j] = j*varslen + i;
		}
	q = q^perm1;
	q = bdd_quantify(q, quants, bits_l, varslen);
	q = q^perm2;
}


//-----------------------------------------------------------------------------

#define DEV

var2space::var2space(varmap &vmh){
	vm = vmh;
}

var2space::~var2space(){
	clear_cons();
}

void var2space::add_cons(int id, spbdd_handle c) {
	if (find(hvars.begin(), hvars.end(), id) == hvars.end())
		hvars.push_back(id);
	ins[vm.at(id)].push_back(c);
}

void var2space::add_cons_neg(int id, spbdd_handle c) {
	if (find(hvars.begin(), hvars.end(), id) == hvars.end())
		hvars.push_back(id);

	outs[vm.at(id)].push_back(c);
}

void var2space::negate_cons() {
	if (nf == C) nf = D;
	else if (nf == D) nf = C;
	swap(ins,outs);
	for (auto &i : bf)
		i.negate_cons();
}

void var2space::clear_cons() {
	hvars.clear();
	ins.clear();
	outs.clear();
}

void var2space::constraint(spbdd_handle q) {

	//TODO review handling of quant unsat
	if ((q == hfalse && nf == C)) clear_cons();
	else if ((q == htrue && nf == D)) clear_cons();
	else if (nf == C) {
		for (auto& [k, v] : ins) {
			for(auto & i : v) i = i && q;
		}
		for (auto& [k, v] : outs) {
			for (auto &i : v) i = i && q;
		}
	}
	else {
		#ifdef DEV
		COUT << "TODO CONSTRAINT" << endl;
		#endif
		;
	}

}

void var2space::merge() {

	if (nf == C) {
		for (auto& [k, v] : ins) {
			if (v.size() > 1) {
				spbdd_handle x = bdd_or_many(v);
				v.clear();
				v.push_back(x);
			}
		}
		for (auto& [k, v] : outs) {
			if (v.size() > 1) {
				spbdd_handle x = bdd_or_many(v);
				v.clear();
				v.push_back(x);
			}
		}
	}

	else {
		#ifdef DEV
		COUT << "TODO MERGE" << endl;
		#endif
		;
	}
}

void var2space::print(int_t level) const {

	string tab(level*4, ' ');
	COUT << tab << "<-----------------------" << endl;
	COUT << tab <<"# var2space cons: l=" << level << ", nf=";
	if (nf == C) COUT << "C\n";
	else COUT << "D\n";

	for (auto const& [k, idx]: vm) {
		COUT << tab << "var2id: " << k << endl;
		if (ins.find(idx) != ins.end()) {
			COUT << tab << "ins: \n";
			for(auto & q : ins.at(idx))
				::out(COUT << tab, q)<<endl;
		}
		if (outs.find(idx) != outs.end()) {
			COUT << tab << "outs: \n";
			for(auto & q : outs.at(idx))
				::out(COUT << tab, q)<<endl;
		}
	}
	COUT << tab << "----------------------->" << endl;
	for (auto &i : bf)
		i.print(level+1);
}

bool var2space::quantify(vector<quant_t> &quantsh) const {

	for (auto &idx : hvars) { 
			if (quantsh[vm.at(idx)] == quant_t::EXH) {
				if (ins.find(vm.at(idx)) != ins.end())
					if (ins.at(vm.at(idx)).size() > 0)
						if (ins.at(vm.at(idx))[0] == hfalse) return false ;
				if (outs.find(vm.at(idx)) != outs.end())
					if (outs.at(vm.at(idx)).size() > 0)
						if (outs.at(vm.at(idx))[0]== htrue) return false ;
			}
			else if (quantsh[vm.at(idx)] == quant_t::FAH) {
				if (outs.find(vm.at(idx)) != outs.end())
					if (outs.at(vm.at(idx)).size() > 0)
						if (outs.at(vm.at(idx))[0] != hfalse) return false ;
			}
			else assert(false);
	}
	return true;
}

