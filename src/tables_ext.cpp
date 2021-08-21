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
#include <list>
#include "tables.h"
#include "dict.h"
#include "input.h"
#include "output.h"
using namespace std;

//#define L2
#ifdef L2
	#define DBG2(x) x
#else
	#define DBG2(x) ;
#endif

typedef tuple<size_t, size_t, size_t, int_t, uint_t, uint_t> alumemo;
map<alumemo, spbdd_handle> carrymemo;
map<alumemo, spbdd_handle> addermemo;

extern uints perm_init(size_t n);

map<term, spbdd_handle> cs_addermemo;
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// general arithmetic

void tables::set_constants(const term& t, spbdd_handle &q) const {
	size_t args = t.size();
	for (size_t i = 0; i< args; ++i)
		if (t[i] >= 0) {
			spbdd_handle aux = from_sym(i, args, t[i]);
			q = q && aux;
		}
	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
		for (size_t j = 0; j< args; ++j)
			if (t[j] >= 0) exvec.push_back(true);
			else exvec.push_back(false);
	}
	q = q/exvec;
}
// ----------------------------------------------------------------------------
bool tables::handler_arith(const term &t, const varmap &vm, const size_t vl,
		spbdd_handle &c) {

	spbdd_handle q = bdd_handle::T;
	switch (t.arith_op) {
		case ADD:
		{
			static map<term, spbdd_handle>::const_iterator it;
			if ((it = cs_addermemo.find(t)) != cs_addermemo.end()) {
				q = it->second;
				//still not optimal, t may contain different var id, but result in same adder
			} else {
				size_t args = 3;
				q = add_var_eq(0, 1, 2, args);
				set_constants(t,q);
				cs_addermemo.emplace(t,q);
			}
			//var alignment with head
			uints perm2 = get_perm(t, vm, vl);
			q = q^perm2;
		} break;
		case SHR:
		{
			size_t var0 = vm.at(t[0]);
			//TODO: move check to parser
			DBG(assert(t[1] > 0 && "shift value must be a constant");)
			size_t num1 = t[1] >> 2;
			size_t var2 = vm.at(t[2]);
			q = shr(var0, num1, var2, vl);
		} break;
		case SHL:
		{
			size_t var0 = vm.at(t[0]);
			//TODO: move check to parser
			DBG(assert(t[1] > 0 && "shift value must be a constant");)
			size_t num1 = t[1] >> 2;
			size_t var2 = vm.at(t[2]);
			q = shl(var0, num1, var2, vl);
		} break;

		case MULT:
		{
			size_t args = t.size();
			//single precision args = 3, double precision args = 4
			if (args == 3) q = mul_var_eq(0,1,2,3);
			else if (args == 4) q = mul_var_eq_ext(0,1,2,3,args);
			DBG(else assert(false);) //TODO: move check to parser
			set_constants(t,q);
			uints perm2 = get_perm(t, vm, vl);
			q = q^perm2;
		} break;

		default: break;
	};
	c = c && q;
	return true;
}

// -----------------------------------------------------------------------------
// adder
spbdd_handle tables::full_addder_carry(size_t var0, size_t var1, size_t n_vars,
		uint_t b, spbdd_handle r) const {
	if (b == 1) return bdd_handle::F;
	return bdd_ite(full_addder_carry(var0, var1, n_vars, b-1, r),
					bdd_ite(::from_bit(pos(b, var0, n_vars),true),
							bdd_handle::T, ::from_bit(pos(b, var1, n_vars),true)),
					bdd_ite(::from_bit(pos(b, var0, n_vars),true),
							::from_bit(pos(b, var1, n_vars),true), bdd_handle::F));
}

spbdd_handle tables::full_adder(size_t var0, size_t var1, size_t n_vars,
		uint_t b) const {
	if (b < 2)
		return ::from_bit( pos(b, var0, n_vars),true)
				&& ::from_bit( pos(b, var1, n_vars),true);
	else if (b == 2)
		return bdd_ite(::from_bit(pos(b, var0, n_vars),true),
									::from_bit(pos(b, var1, n_vars),false),
									::from_bit(pos(b, var1, n_vars),true));

	spbdd_handle carry = bdd_handle::F;
	carry = full_addder_carry(var0, var1, n_vars, b-1, carry);
	return bdd_ite(
			carry,
			bdd_ite(::from_bit(pos(b, var0, n_vars),true),
					::from_bit(pos(b, var1, n_vars),true),
					::from_bit(pos(b, var1, n_vars),false)),
			bdd_ite(::from_bit(pos(b, var0, n_vars),true),
					::from_bit( pos(b, var1, n_vars),false),
					::from_bit( pos(b, var1, n_vars),true))
			);
}

spbdd_handle tables::add_var_eq(size_t var0, size_t var1, size_t var2,
		size_t n_vars) {
	spbdd_handle r = bdd_handle::T;
	for (size_t b = 0; b != bits; ++b) {
		spbdd_handle fa = bdd_handle::T;
		if (b == 0) {
			fa = ::from_bit(pos(b, var0, n_vars),false) &&
					::from_bit(pos(b, var1, n_vars),false);
			r = fa && ::from_bit(pos(b, var2, n_vars),false);
		}
		else if (b == 1) {
			fa = ::from_bit(pos(b, var0, n_vars),true) &&
					::from_bit(pos(b, var1, n_vars),true);
			r = r && fa && ::from_bit(pos(b, var2, n_vars),true);
		}
		else {
			fa = full_adder( var0, var1, n_vars , b);
			r = r && bdd_ite(fa , ::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));
		}
	}
 	return r;
}

// ----------------------------------------------------------------------------
// multiplier
spbdd_handle tables::add_ite_carry(size_t var0, size_t var1, size_t n_vars,
		uint_t i, uint_t j) {
	static alumemo x;
	static map<alumemo, spbdd_handle>::const_iterator it;
	if ((it = carrymemo.find(x = { var0, var1, n_vars, bits, i, j })) !=
			carrymemo.end()) return it->second;
	spbdd_handle r;
	//extended precision support
	if (i == 2 || j == 2) {
		r = bdd_handle::F;
	}
	//-
	else {
		spbdd_handle acc_i = add_ite(var0, var1, n_vars, i, j-1);
		spbdd_handle bit = ::from_bit(pos(j, var0, n_vars),true) &&
				::from_bit(pos(i-j+2, var1, n_vars),true);
		if (i == j) {
			r = acc_i && bit;
		}
		else {
			spbdd_handle carry_j = add_ite_carry(var0, var1, n_vars,i-1,j);
			r = bdd_ite(bit, acc_i || carry_j, acc_i && carry_j);
		}
	}
	return carrymemo.emplace(x, r), r;
}

spbdd_handle tables::add_ite(size_t var0, size_t var1, size_t n_vars, uint_t i,
		uint_t j) {
	static alumemo x;
	static map<alumemo, spbdd_handle>::const_iterator it;
	if ((it = addermemo.find(x = { var0, var1, n_vars, bits, i, j })) !=
			addermemo.end()) return it->second;
	spbdd_handle r;
	//extended precision support
	if (i - j == bits - 2) {
		r = add_ite_carry(var0, var1, n_vars,i-1,j);
	}
	else if (i == 2 || j == 2) {
			r = ::from_bit(pos(j, var0, n_vars),true) &&
					::from_bit(pos(i, var1, n_vars),true);
	}
	else if (i == j) {
		spbdd_handle bit = ::from_bit(pos(j, var0, n_vars),true)
				&& ::from_bit(pos(i-j+2, var1, n_vars),true);
		spbdd_handle acc_i = add_ite(var0, var1, n_vars, i, j-1);
		r =  bdd_xor(bit, acc_i);
	}
	else  { //(i != j)
		spbdd_handle bit = ::from_bit(pos(j, var0, n_vars),true)
				&& ::from_bit(pos(i-j+2, var1, n_vars),true);
		spbdd_handle acc_i = add_ite(var0, var1, n_vars, i, j-1);
		spbdd_handle carry_ij = add_ite_carry(var0, var1, n_vars,i-1,j);
		spbdd_handle bout =
				bdd_ite( bit ,
						bdd_ite(acc_i ,
								bdd_ite(carry_ij, bdd_handle::T, bdd_handle::F),
								bdd_ite(carry_ij, bdd_handle::F, bdd_handle::T)),
						bdd_ite(acc_i ,
								bdd_ite(carry_ij, bdd_handle::F, bdd_handle::T),
								bdd_ite(carry_ij, bdd_handle::T, bdd_handle::F))
					);
		r =  bout;
	}
	return addermemo.emplace(x, r), r;
}

spbdd_handle tables::mul_var_eq(size_t var0, size_t var1, size_t var2,
			size_t n_vars) {

	spbdd_handle r = bdd_handle::T;
	r = r && ::from_bit(pos(0, var0, n_vars),false) &&
			 ::from_bit(pos(0, var1, n_vars),false) &&
			 ::from_bit(pos(0, var2, n_vars),false);
	r = r && ::from_bit(pos(1, var0, n_vars),true) &&
			 ::from_bit(pos(1, var1, n_vars),true) &&
			 ::from_bit(pos(1, var2, n_vars),true);

	for (size_t b = 2; b < bits; ++b) {
		spbdd_handle acc_bit = bdd_handle::F;
		acc_bit = add_ite(var0, var1, n_vars, b, b);
		//equality
		r = r && bdd_ite(acc_bit ,
				::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));
	}
	return r;
}

spbdd_handle tables::mul_var_eq_ext(size_t var0, size_t var1, size_t var2,
		size_t var3, size_t n_vars) {

	spbdd_handle r = bdd_handle::T;
	r = r && ::from_bit(pos(0, var0, n_vars),false) &&
			 ::from_bit(pos(0, var1, n_vars),false) &&
			 ::from_bit(pos(0, var2, n_vars),false) &&
			 ::from_bit(pos(0, var3, n_vars),false);
	r = r && ::from_bit(pos(1, var0, n_vars),true) &&
			 ::from_bit(pos(1, var1, n_vars),true) &&
			 ::from_bit(pos(1, var2, n_vars),true) &&
			 ::from_bit(pos(1, var3, n_vars),true);
	for (size_t b = 2; b < bits; ++b) {
		spbdd_handle acc_bit = bdd_handle::F;
		acc_bit = add_ite(var0, var1, n_vars, b, b);
		//equality
		r = r && bdd_ite(acc_bit ,
				::from_bit(pos(b, var3, n_vars), true),
				::from_bit(pos(b, var3, n_vars), false));
	}
	for (size_t b = 2; b < bits; ++b) {
		spbdd_handle acc_bit = bdd_handle::F;
		acc_bit = add_ite(var0, var1, n_vars, bits + (b-2) , bits-1);
		//equality
		r = r && bdd_ite(acc_bit ,
				::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));
	}
	return r;
}
// ----------------------------------------------------------------------------

//shr for equality
spbdd_handle tables::shr(size_t var0, size_t n, size_t var2, size_t n_vars) {

	spbdd_handle s = bdd_handle::T;
	if (n <= bits-2) {
		s = from_sym_eq(var0, var2, n_vars);
		bools exvec;
		for (size_t i = 0; i < (n_vars*bits); i++)
			if (i < n_vars*n)
				exvec.push_back(true);
			else exvec.push_back(false);
		s = s / exvec;

		uints perm1;
		perm1 = perm_init(n_vars*bits);
		for (size_t i = bits-2-1; i >= n; i--)
			for (size_t j = 0; j < n_vars; ++j) {
				if (j == var0)
					perm1[i*n_vars+j] = perm1[(i-n)*n_vars+j];
		}
		s = s^perm1;
		for(size_t i = 0; i < n; i++)
			s = s && ::from_bit(pos(bits-1-i, var2, n_vars), false);
	} else {
		for(size_t i = 0; i < bits-2; i++)
			s = s && ::from_bit(pos(bits-1-i, var2, n_vars), false);
	}
	return s && constrain_to_num(var0, n_vars) &&
		constrain_to_num(var2, n_vars);
}

//shl for equality
spbdd_handle tables::shl(size_t var0, size_t n, size_t var2,
		size_t n_vars)  {

	spbdd_handle s = bdd_handle::T;

	if (n <= bits-2) {

		s = from_sym_eq(var0, var2, n_vars);

		//XXX: before permuting(shifting) the equality is mandatory
		//     to remove all bits that won't be part of it
		bools exvec;
		for (size_t i = 0; i < (n_vars*bits); i++)
			if (i >= n_vars*(bits-2-n) && i < n_vars*(bits-2) )
				exvec.push_back(true);
			else exvec.push_back(false);
		s = s / exvec;

		uints perm1;
		perm1 = perm_init(n_vars*bits);
		for (size_t i = 0; i < bits-2-n; i++)
			for (size_t j = 0; j < n_vars; ++j) {
				if (j == var0 )
					perm1[i*n_vars+j] = perm1[(i+n)*n_vars+j];
				//COUT << i*n_vars+j+1 << "--" << perm1[i*n_vars+j]+1 << endl;
			}
		s = s^perm1;

		for(size_t i = 0; i < n; i++)
			s = s && ::from_bit(pos(i+2, var2, n_vars), false);

	} else {
		for(size_t i = 0; i < bits-2; i++)
		    	s = s && ::from_bit(pos(i+2, var2, n_vars), false);
	}
	return s && constrain_to_num(var0, n_vars) &&
		constrain_to_num(var2, n_vars);
}

//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
// bitwise operators
t_arith_op tables::get_bwop(lexeme l) {
	if (l == "bw_and")
		return BITWAND;
	else if (l == "bw_or")
		return BITWOR;
	else if (l == "bw_xor")
			return BITWXOR;
	else if (l == "bw_not")
		return BITWNOT;
	else return NOP;
}

// pairwise operators
t_arith_op tables::get_pwop(lexeme l) {
	if (l == "pw_add")
		return ADD;
	else if (l == "pw_mult")
		return MULT;
	else return NOP;
}

// remove type bits
spbdd_handle tables::ex_typebits(size_t in_varid, spbdd_handle in, size_t n_vars) {

	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
		for (size_t j = 0; j< n_vars; ++j)
			if (j == in_varid && (i == bits - 2 || i == bits - 1)) exvec.push_back(true);
			else exvec.push_back(false);
	}
	spbdd_handle out = in / exvec;
	return out;
}

// switch between LS and MS bit ordering
spbdd_handle tables::perm_bit_reverse(spbdd_handle in, size_t n_bits, size_t n_vars) {

	uints perm1;
	perm1 = perm_init(n_bits*n_vars);
	for (size_t i = 0; i < n_bits*n_vars; i++) {
		perm1[i] = ((n_bits-1-(i/n_vars))*n_vars) + i % n_vars;
	}
	return(in^perm1);
}

// bdd var "tanslation"
spbdd_handle tables::perm_from_to(size_t from, size_t to, spbdd_handle in, size_t n_bits,
		size_t n_vars) {

	uints perm1;
	perm1 = perm_init(n_bits*n_vars);
	for (size_t i = 0; i < n_bits; i++) {
		for (size_t j = 0; j < n_vars; ++j) {
			if (j == from ) {
				//COUT << perm1[i*n_vars+j]  << " ** " <<  perm1[i*n_vars+to] << endl;
				perm1[i*n_vars+j] = perm1[i*n_vars+to];
			}
		}
	}
	spbdd_handle out = in ^ perm1;
	return out;
}

// handler for over bdd bitwise operators: AND, OR, XOR, NOT
spbdd_handle tables::bitwise_handler(size_t in0_varid, size_t in1_varid, size_t out_varid,
		spbdd_handle in0, spbdd_handle in1, size_t n_vars, t_arith_op op ) {

	//XXX: actually not required for bitwise operators
	//     removing type bits leaves bits = bits - 2
	spbdd_handle s0 = ex_typebits(in0_varid, in0, n_vars);
	spbdd_handle s1 = ex_typebits(in1_varid, in1, n_vars);

	s0 = perm_from_to(in0_varid, 0, s0, bits-2, n_vars);
	s1 = perm_from_to(in1_varid, 1, s1, bits-2, n_vars);

	spbdd_handle x;
	switch (op) {
		case BITWAND : x = bdd_bitwise_and(s0, s1); break;
		case BITWOR  : x = bdd_bitwise_or(s0, s1); break;
		case BITWXOR : x = bdd_bitwise_xor(s0, s1); break;
		case BITWNOT : x = bdd_bitwise_not(s0); break;
		default 	 : break;
	}
	x = perm_from_to(2, out_varid, x, bits-2, n_vars);

	x = x && ::from_bit(pos(1, out_varid, n_vars),true) &&
			::from_bit(pos(0, out_varid, n_vars),false);

	return x;
}

// handler for over bdd arithmetic operators: ADD, MULT
spbdd_handle tables::pairwise_handler(size_t in0_varid, size_t in1_varid, size_t out_varid,
		spbdd_handle in0, spbdd_handle in1, size_t n_vars, t_arith_op op ) {

	spbdd_handle s0 = ex_typebits(in0_varid, in0, n_vars);
	spbdd_handle s1 = ex_typebits(in1_varid, in1, n_vars);
	s0 = perm_from_to(in0_varid, 0, s0, bits-2, n_vars);
	s1 = perm_from_to(in1_varid, 1, s1, bits-2, n_vars);
	s0 = perm_bit_reverse(s0, bits-2, n_vars);
	s1 = perm_bit_reverse(s1, bits-2, n_vars);
	spbdd_handle x;
	switch (op) {
		case ADD : x = bdd_adder(s0, s1); break;
		case MULT: x = bdd_mult_dfs(s0, s1, bits-2,3); break;
		default  : break;
	}
	x = perm_bit_reverse( x, bits-2, n_vars);
	x = perm_from_to(2, out_varid, x, bits-2, n_vars);
	x = x && ::from_bit(pos(1, out_varid, n_vars),true) &&
			::from_bit(pos(0, out_varid, n_vars),false);
	return x;
}

//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
// fol support

pair<bools, uints> tables::deltail(size_t len1, size_t len2, size_t bits) const {
	bools ex(len1 * bits, false);
	uints perm = perm_init(len1 * bits);
	for (size_t n = 0; n != len1; ++n)
		for (size_t k = 0; k != bits; ++k)
			if (n >= len2) ex[pos(k, bits, n, len1)] = true;
			else perm[pos(k,bits,n, len1)] = pos(k,bits, n, len2);
	return { ex, perm };
}

uints tables::get_perm(const term& t, const varmap& m, size_t len, size_t bits) const {
	uints perm = perm_init(t.size() * bits);
	for (size_t n = 0, b; n != t.size(); ++n)
		if (t[n] < 0)
			for (b = 0; b != bits; ++b)
				perm[pos(b,bits,n,t.size())] = pos(b,bits,m.at(t[n]),len);
	return perm;
}

void tables::ex_typebits(spbdd_handle &s, size_t nvars) const {
	bools exvec;
	for (size_t i = 0; i < bits; ++i)
		for (size_t j = 0; j< nvars; ++j)
			if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
			else exvec.push_back(false);
	s = s / exvec;
}

void tables::ex_typebits(bools &exvec, size_t nvars) const {
	for (size_t i = 0; i < bits; ++i)
		for (size_t j = 0; j< nvars; ++j)
			if (i == bits - 2 || i == bits - 1 )
				exvec[i*nvars+j]=true;
}

void tables::append_num_typebits(spbdd_handle &s, size_t nvars) const {
	for (size_t j = 0; j < nvars; ++j)
		s = s && ::from_bit(pos(1, j, nvars),1) && ::from_bit(pos(0, j, nvars),0);
}
//-----------------------------------------------------------------------------
void tables::handler_formh(pnft_handle &p, form *f, varmap &vm, varmap &vmh) {
	//is_horn = true;
	switch (f->type) {
		case form::EXISTS1:
		case form::FORALL1:
		case form::UNIQUE1:
			handler_form1(p, f, vm, vmh, true); break;

		case form::EXISTS2:
		case form::FORALL2:
		case form::UNIQUE2: {
			//XXX: handle variables used in q's more than once?
			vmh.emplace(f->l->arg, vmh.size());
			for (auto &v : vmh)
				v.second = vmh.size()-1-v.second;
			p->vmh = vmh;
			p->quantsh.emplace(p->quantsh.begin(), p->to_quant_t(f));
			handler_formh(p, f->r,vm, vmh);
			//vmh.erase(f->l->arg);
		} break;
		default: break;
	}
	//is_horn = false;
	//TODO: create VAR2 structures
}


void tables::handler_form1(pnft_handle &p, form *f, varmap &vm, varmap &vmh, bool fq) {

	DBG(assert(
			(f->type == form::ATOM && f->l == NULL && f->r == NULL) ||
			(f->type == form::NOT  && f->l != NULL && f->r == NULL) ||
			((f->type == form::AND || f->type == form::OR || f->type == form::IMPLIES) && f->l != NULL && f->r != NULL) ||
			((f->type == form::EXISTS1 || f->type == form::FORALL1) || (f->type == form::UNIQUE1) && f->r != NULL)
		));

	if (f->type == form::ATOM) {
		//assuming no free variables in qbf
		//TODO: assert to check free vars
		pnft_handle p0(new(pnft));
		if (f->tm->extype == term::REL) {
			if ( vmh.find(f->arg) == vmh.end() ) { /*f->arg <= 0*/
				DBG(assert(f->tm->neg == false);)
				p0->b = new body(get_body(*f->tm, vm, vm.size()));
				//DBG(assert(p0->b->neg == false);)
				ex_typebits(p0->b->ex, f->tm->size());
				static set<body*, ptrcmp<body>>::const_iterator bit;
				if ((bit = p->bodies.find(p0->b)) == p->bodies.end())
					p->bodies.insert(p0->b);
			} else {
				DBG(assert(f->tm->neg == false);)
				body *aux = new body(get_body(*f->tm, vm, vm.size()));
				ex_typebits(aux->ex, f->tm->size());
				std::pair<int_t, body*> hvar = {f->arg, move(aux)};
				p0->hvar_b = hvar;
			}
		}
		else if (f->tm->extype == term::ARITH) {
			DBG(assert(f->tm->neg == false));
			handler_arith(*f->tm, vm, vm.size(), p0->cons);
			ex_typebits(p0->cons, vm.size());
		}
		else if (f->tm->extype == term::EQ) {
			if (f->tm->neg) f->tm->neg = false, p0->neg = true;
			handler_eq(*f->tm, vm, vm.size(), p0->cons);
			ex_typebits(p0->cons, vm.size());
		}
		else if (f->tm->extype == term::LEQ) {
			if (f->tm->neg) f->tm->neg = false, p0->neg = true;
			handler_leq(*f->tm, vm, vm.size(), p0->cons);
			ex_typebits(p0->cons, vm.size());
		}
		else {
			p0->cons =  bdd_ite(::from_bit(0,true), bdd_handle::T, bdd_handle::F);
			uints perm = get_perm(*f->tm, vm, vm.size());
			p0->cons  = p0->cons^perm;
			ex_typebits(p0->cons, vm.size());
		}
		//TODO: intersect consts
		p->matrix.push_back(p0);

	}
	else if (f->type == form::IMPLIES) {
		if (f->l->type == form::ATOM) {
			handler_form1(p, f->l,vm,vmh,fq);
		} else {
			pnft_handle p0(new(pnft));
			handler_form1(p0, f->l,vm, vmh,fq);
			p->bodies.insert(p0->bodies.begin(), p0->bodies.end());
			p->matrix.push_back(p0);
		}
		if (f->r->type == form::ATOM) {
			handler_form1(p, f->r,vm,vmh,fq);
			p->matrix[p->matrix.size()-1]->neg = true;
		} else {
			pnft_handle p1(new(pnft));
			handler_form1(p1, f->r,vm,vmh,fq);
			p1->neg = !p1->neg;
			p->bodies.insert(p1->bodies.begin(), p1->bodies.end());
			p->matrix.push_back(p1);
		}
		p->neg = !p->neg;
	}
	//else if (f->type == form::COIMPLIES){}
	else if (f->type == form::AND) {
		if (f->l->type == form::AND || f->l->type == form::ATOM  || f->l->type == form::NOT) {
			handler_form1(p, f->l,vm, vmh,fq);
		} else {
			pnft_handle p0(new(pnft));
			handler_form1(p0, f->l,vm, vmh,fq);
			p->bodies.insert(p0->bodies.begin(), p0->bodies.end());
			p->matrix.push_back(p0);
		}
		if (f->r->type == form::AND || f->r->type == form::ATOM  || f->r->type == form::NOT) {
			handler_form1(p, f->r,vm, vmh,fq);
		} else {
			pnft_handle p1(new(pnft));
			handler_form1(p1, f->r,vm, vmh,fq);
			p->bodies.insert(p1->bodies.begin(), p1->bodies.end());
			p->matrix.push_back(p1);
		}
	}
	else if (f->type == form::OR) {
		if (f->l->type == form::OR || f->l->type == form::ATOM  || f->l->type == form::NOT) {
			size_t aux = p->matrix.size();
			handler_form1(p, f->l,vm, vmh,fq);
			if (f->l->type != form::OR)
				p->matrix[aux]->neg = !p->matrix[aux]->neg;
		} else {
			pnft_handle p0(new(pnft));
			handler_form1(p0, f->l,vm, vmh,fq);
			p0->neg = !p0->neg;
			p->bodies.insert(p0->bodies.begin(), p0->bodies.end());
			p->matrix.push_back(p0);
		}
		if (f->r->type == form::OR || f->r->type == form::ATOM  || f->r->type == form::NOT) {
			size_t aux = p->matrix.size();
			handler_form1(p, f->r,vm, vmh,fq);
			if (f->r->type != form::OR)
				p->matrix[aux]->neg = !p->matrix[aux]->neg;
		} else {
			pnft_handle p1(new(pnft));
			handler_form1(p1, f->r,vm, vmh,fq);
			p1->neg = !p1->neg;
			p->bodies.insert(p1->bodies.begin(), p1->bodies.end());
			p->matrix.push_back(p1);
		}
		p->neg = true;
	}
	else if (f->type == form::NOT) {
		if (f->l->type == form::ATOM || f->l->type == form::NOT) {
			handler_form1(p, f->l, vm,vmh,fq);
			if (f->l->type == form::ATOM) p->matrix[p->matrix.size()-1]->neg = !p->matrix[p->matrix.size()-1]->neg;
			else if (f->l->type == form::NOT) p->neg = !p->neg;
		} else if (f->l->type == form::AND || f->l->type == form::IMPLIES){
			pnft_handle p0(new(pnft));
			p0->neg = true;
			handler_form1(p0, f->l, vm,vmh,fq);
			p->matrix.push_back(p0);
		} else { //is quant/or
			pnft_handle p0(new(pnft));
			p0->neg = true;
			pnft_handle p1(new(pnft));
			handler_form1(p1, f->l, vm,vmh,fq);
			p0->matrix.push_back(p1);
			p->matrix.push_back(p0);
		}
	}
	else if (f->type == form::EXISTS1 || f->type == form::FORALL1 || f->type == form::UNIQUE1) {
		varmap tmpvm;
		if (fq)	tmpvm = vm;
		if (vm.find(f->l->arg) != vm.end()) {
			for (auto &v : vm)
				if (v.first != f->l->arg && v.second == p->quants.size())
					v.second++;
			vm.at(f->l->arg) = p->quants.size();
		}
		else {
			for (auto &v : vm)
				if (v.first != f->l->arg && v.second >= p->quants.size())
					v.second++;
			vm.emplace(f->l->arg, p->quants.size());
		}
		p->quants.push_back(p->to_quant_t(f));

		if(!(f->r->type == form::EXISTS1 || f->r->type == form::FORALL1 ||
				f->r->type == form::UNIQUE1)) {
			handler_form1(p, f->r,vm, vmh, true);
		} else
			handler_form1(p, f->r,vm, vmh, false);

		if(fq) {
			p->varslen = vm.size();
			if (vm.size() > 0) {
				varmap aux = tmpvm;
				for (auto &v : vm)
					if (aux.find(v.first) == aux.end()) {
						aux.emplace(v.first, aux.size());
					}
				term t; t.resize(vm.size());
				for (auto &v : vm) t[v.second] = v.first;
				p->perm = get_perm(t, aux, vm.size(), bits-2);
				vm = tmpvm; //for nested formulas
			}
			//TODO: group all negs, all pos
		}
	}
}

//-----------------------------------------------------------------------------
void tables::fol_query(cr_pnft_handle f, bdd_handles &v) {

	if (f->bodies.size() != 0 && f->fp(this)) {
		v.push_back(f->last);
		//DBG(COUT << " hit memos fol\n");
		return;
	}
	spbdd_handle q = htrue;
	for (auto p : f->matrix) {
		if (p->b) {
			q = body_query(*p->b,0);
			if (p->neg) q = bdd_not(q);
			v.push_back(q);
		} else if (p->cons != bdd_handle::T) {
			q = p->cons;
			if (p->neg) q = bdd_not(q);
			v.push_back(q);
		}
		else {
			bdd_handles vt;
			fol_query(p,vt);
			//DBG(assert(vt.size() == 1);) // fails when using IF command
			v.insert(v.end(), vt.begin(), vt.end());
		}
	}
	//if (v.size() > 1)
	q = bdd_and_many(move(v));
	if (f->neg) q = bdd_not(q);

	if (f->quants.size() != 0) {
		//TODO: move perms inits to preparation
		uints perm1 = perm_init((bits-2)*f->varslen);
		uints perm2 = perm_init((bits-2)*f->varslen);
		for (size_t i = 0; i < f->varslen; i++)
			for (size_t j = 0; j < bits-2; j++) {
				perm1[j * f->varslen + i] = i*(bits-2)+j;
				perm2[i*(bits-2)+j] = j*f->varslen + i;
			}
		q = q^perm1;
		q = bdd_quantify(q, f->quants, bits-2, f->varslen);
		q = q^perm2;
	}

	//realign variables
	if (f->perm.size()!= 0) {
		q = q^f->perm;
		v.push_back(q);
	}
	if (f->perm_h.size()!= 0)
		q = bdd_and_many_ex_perm(move(v), f->ex_h,f->perm_h);
	f->last = q;
	v.push_back(q);
}

// Work in progress
#define sohorn_query hol_query
void tables::hol_query(cr_pnft_handle f, bdd_handles &v, bdd_handles &vh,
		std::vector<bdd_handles> &hvar_hbdd, std::vector<quant_t> &quantsh, varmap &vmh ) {

	spbdd_handle q = htrue;
	spbdd_handle qh = htrue;

	for (auto p : f->matrix) {
			if (p->b) {
				q = body_query(*p->b,0);
				if (p->neg) q = bdd_not(q);
				v.push_back(q);
			} else if (p->cons != bdd_handle::T) {
				v.push_back(p->cons);
			}
			else if(p->hvar_b.second != 0) {
				if (quantsh[vmh[p->hvar_b.first]] == EXH) {

					//pr(p->hvar_b.second->q, vh[p->hvar_b.first-1], hvar_hbdd[0], p->neg);
					//in case hvar is set as a table:
					//qh = body_query(*f->hvar_b.second,0);
					spbdd_handle c = htrue;
					auto b = *p->hvar_b.second;
					//COUT << "R0" << ::bdd_root(b.q) << " :\n";
					//::out(COUT, b.q)<<endl<<endl;
					qh = bdd_and_ex_perm(c, b.q, b.ex, b.perm);
					if (f->neg) qh = bdd_not(qh);
					//COUT << "R1" << ::bdd_root(qh) << " :\n";
					//::out(COUT, qh)<<endl<<endl;
					vh.push_back(qh);
				}
			}
			else {
				bdd_handles vt, vth;
				hol_query(p,vt,vth, hvar_hbdd, quantsh,vmh);
				DBG(assert(vt.size() <= 1 && vt.size() <= 1);)
				v.insert(v.end(), vt.begin(), vt.end());
				vh.insert(vh.end(), vth.begin(), vth.end());
			}
	}

	if (v.size() > 1) {
		q = bdd_and_many(move(v));
		if (f->neg) q = bdd_not(q);
		v.push_back(q);
	}
	if (vh.size() > 1) {
		qh = bdd_and_many(move(vh));
		if (f->neg) qh = bdd_not(qh);
		//COUT << "R2 " << ::bdd_root(qh) << " :\n";
		//::out(COUT, qh)<<endl<<endl;
		vh.push_back(qh);
	}
	return;
}

void tables::formula_query(cr_pnft_handle f, bdd_handles &v) {
	if (f->quantsh.size() != 0) {
		//for basic hbdd
		//bdd_handles v1;
		//bdd_handles v2;
		//std::vector<bdd_handles> hvar_hbdd(1);
		bdd_handles v1;
		bdd_handles v2;
		bdd_handles vh(f->quantsh.size(), htrue);
		std::vector<bdd_handles> hvar_hbdd;
		hvar_hbdd.push_back(vh);

		sohorn_query(f, v1, v2, hvar_hbdd, f->quantsh, f->vmh);
		//COUT << " so_horn " << ::bdd_root(v2[0]) << " :\n";
		//::out(COUT, v2[0])<<endl<<endl;
		spbdd_handle q;
		q = (v2.size()!= 0 ? v2[0] : hfalse) % (v1.size() != 0 ? v1[0] : hfalse);
		v.push_back(q);
	}
	else fol_query(f,v);
}
