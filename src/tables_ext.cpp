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
#include "tables.h"
#include "dict.h"
#include "input.h"
#include "output.h"
using namespace std;

typedef tuple<size_t, size_t, size_t, int_t, uint_t, uint_t> alumemo;
map<alumemo, spbdd_handle> carrymemo;
map<alumemo, spbdd_handle> addermemo;

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

extern uints perm_init(size_t n);

// ----------------------------------------------------------------------------

void tables::ex_typebits(spbdd_handle &s, size_t nvars) const {
	bools exvec;
	for (size_t i = 0; i < bits; ++i)
		for (size_t j = 0; j< nvars; ++j)
			if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
			else exvec.push_back(false);
	s = s / exvec;
}

void tables::append_num_typebits(spbdd_handle &s, size_t nvars) const {
	for (size_t j = 0; j< nvars; ++j)
		s = s && ::from_bit(pos(1, j, nvars),1)
			  && ::from_bit(pos(0, j, nvars),0);
}

void tables::perm_qvar(spbdd_handle &s, size_t var, size_t nvars) const {

	uints perm = perm_init(bits*nvars);
	perm[0] = var;
	//TODO: put var first
	/*
	for (size_t i = 0; i < n_bits*n_vars; i++) {
		perm1[i] = ((n_bits-1-(i/n_vars))*n_vars) + i % n_vars;
	}
	*/
	s = s^perm;
}

//-----------------------------------------------------------------------------

spbdd_handle tables::fol_eval(form *f) {

	assert(f!=NULL);

	//NONE, ATOM, FORALL1, EXISTS1, UNIQUE1, AND, OR, NOT, IMPLIES, COIMPLIES
	//FORALL2, EXISTS2, UNIQUE2
	DBG(assert((f->type == form::ATOM && f->l == NULL && f->r == NULL) || \
		   (f->type == form::NOT  && f->l != NULL && f->r == NULL) || \
		   (f->l != NULL && f->r != NULL)));

	spbdd_handle q = htrue;

	//TODO: properly bring nvars here
	size_t nvars = 1;

	switch (f->type) {
		case form::ATOM:
			DBG(assert(f->arg == 0));

			q = tbls[f->tm->tab].t;
			//set_constants(t,a,q);
			//b.perm = get_perm(t, vm, len), //check get_body
			ex_typebits(q, nvars);
			o::dbg() << L" ------------------- " << ::bdd_root(q) << L" :\n";
			::out(wcout, q)<<endl<<endl;
			append_num_typebits(q,nvars);
			break;

		case form::IMPLIES:
			//XXX: review how to deal with different arity
			q = bdd_impl(fol_eval(f->l), fol_eval(f->r));

			ex_typebits(q, nvars);
			o::dbg() << L" implies ------------------- " << ::bdd_root(q) << L" :\n";
			::out(wcout, q)<<endl<<endl;
			append_num_typebits(q,nvars);
			break;

		case form::COIMPLIES: /*q = bdd_coimpl(fol_eval(f->l), fol_eval(f->l));*/ break;
		case form::AND: q = fol_eval(f->l) && fol_eval(f->r); break;
		case form::OR: q = fol_eval(f->l) && fol_eval(f->r); break;
		case form::NOT: q = bdd_not(fol_eval(f->l)); break;

		case form::EXISTS1: ;
			  //b.insert(lastbody = { get_body(t, a.vm, a.varslen), t });
			  //permute according to ?x
			  //bdd_or
			  //undo permute or register perm as in body
			break;

		case form::FORALL1: ;
			q = fol_eval(f->r);
			//TOO: permute according to: f->l->arg
			o::dbg() << L" in forall ------------------- " << ::bdd_root(q) << L" :\n";
			::out(wcout, q)<<endl<<endl;
			ex_typebits(q, nvars);
			q = bdd_and_hl(q);
			append_num_typebits(q,nvars);
			o::dbg() << L" out forall ------------------- " << ::bdd_root(q) << L" :\n";
						::out(wcout, q)<<endl<<endl;
			break;

		case form::UNIQUE1: ; break;

		default: break;

	}

	return q;
}

bool tables::handler_form1(const term& t, alt& a, spbdd_handle &cons) {
	DBG(assert(a.varslen != 0));
	cons = fol_eval(t.qbf);
	o::dbg() << L" ---------%%%%---------- " << ::bdd_root(cons) << L" :\n";
	::out(wcout, cons)<<endl<<endl;
	return true;
}

// ----------------------------------------------------------------------------
// XXX: will deprecate?
uints tables::get_perm_ext(const term& t, const varmap& m, size_t len) const {
	uints perm = perm_init(len * bits);
	for (size_t n = 0, b; n != len; ++n)
		if (t[n] < 0)
			for (b = 0; b != bits; ++b)
				perm[pos(b,n,len)] = pos(b,m.at(t[n]),len);
	return perm;
}

spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args, size_t bit,
	spbdd_handle x)
	const {
	if (!--bit)
		return	bdd_ite(::from_bit(pos(0, arg2, args), true),
				x,
				x && ::from_bit(pos(0, arg1, args), false));
	return	bdd_ite(::from_bit(pos(bit, arg2, args), true),
			bdd_ite_var(pos(bit, arg1, args),
				leq_var(arg1, arg2, args, bit) && x, x),
			bdd_ite_var(pos(bit, arg1, args), hfalse,
				leq_var(arg1, arg2, args, bit) && x));
}

void tables::set_constants(const term& t, alt& a, spbdd_handle &q) const {

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

	//XXX: this is not part of constants, this is var alignment with head
	uints perm2 = get_perm(t, a.vm, a.varslen);
	q = q^perm2;
}

// ----------------------------------------------------------------------------

bool tables::handler_arith(const term& t, alt& a, spbdd_handle &leq) {


	//DBG(o::dbg() << "ARITH handler ... " << endl;)

	spbdd_handle q;

	switch (t.arith_op) {
		case ADD:
		{
			/*
			if (t[0] >= 0 && t[1] >= 0 && t[2] >= 0) {
				//all NUMS
				if ( (t[0] >> 2) + (t[1] >> 2) != (t[2] >> 2)) return false;
				return true;
			}
			else if (t[0] < 0 && t[1] >= 0 && t[2] >= 0 ) {
				//VAR + CONST = CONST
				size_t bit_0 = a.vm.at(t[0]);
				//q = add_var_const_eq_const(bit_0, a.varslen, t[1], t[2]);
			}
			else if (t[0] < 0 && t[1] >= 0 && t[2] < 0 ) {
				//VAR + CONST = VAR
				size_t bit_0 = a.vm.at(t[0]);
				size_t bit_2 = a.vm.at(t[2]);
				//q = add_var_const_eq_var(bit_0, bit_2, a.varslen, t[1]);
			}
			else if (t[0] < 0 && t[1] < 0 && t[2] < 2) {
				//all VARS
				size_t bit_0 = a.vm.at(t[0]);
				size_t bit_1 = a.vm.at(t[1]);
				size_t bit_2 = a.vm.at(t[2]);
				q = add_var_eq(bit_0, bit_1, bit_2, a.varslen);
			}
			*/
			//all types of addition handled by add_var
			//XXX not working for ?x + ?x = 2
			size_t args = 3;
			q = add_var_eq(0, 1, 2, args);
			set_constants(t,a,q);

		} break;

		case SHR:
		{
			//DBG(o::dbg() << "SHL handler ... " << endl;)
			size_t var0 = a.vm.at(t[0]);
			assert(t[1] > 0 && "shift value must be a constant");
			size_t num1 = t[1] >> 2;
			size_t var2 = a.vm.at(t[2]);
			q = shr(var0, num1, var2, a.varslen);
		} break;

		case SHL:
		{
			//DBG(o::dbg() << "SHL handler ... " << endl;)
			size_t var0 = a.vm.at(t[0]);
			assert(t[1] > 0 && "shift value must be a constant");
			size_t num1 = t[1] >> 2;
			size_t var2 = a.vm.at(t[2]);
			q = shl(var0, num1, var2, a.varslen);

		} break;

		case MULT:
		{
			//DBG(o::dbg() << "MULT handler ... " << endl;)

			size_t args = t.size();

			if (args == 3) {
				q = mul_var_eq(0,1,2,3);
				set_constants(t,a,q);
			}
			//XXX: hook for extended precision
			//XXX wont run, needs update in parser like ?x0:?x1
			else if (args == 4) {
				q = mul_var_eq_ext(0,1,2,3,args);
				set_constants(t,a,q);
			}

		} break;

		default:
			break;

	}

	leq = leq && q;

	return true;

}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// general adder

spbdd_handle tables::full_addder_carry(size_t var0, size_t var1, size_t n_vars,
		uint_t b, spbdd_handle r) const {

	if (b == 1) return bdd_handle::F;

	return bdd_ite( full_addder_carry(var0, var1, n_vars, b-1, r),
					bdd_ite( ::from_bit(pos(b, var0, n_vars),true),
							 bdd_handle::T,
							 ::from_bit(pos(b, var1, n_vars),true)),
					bdd_ite( ::from_bit(pos(b, var0, n_vars),true),
							::from_bit(pos(b, var1, n_vars),true),
							 bdd_handle::F));
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
			/*
			fa = bdd_ite(::from_bit(pos(b, var0, n_vars),false),
					 	 ::from_bit(pos(b, var1, n_vars),false),
						  bdd_handle::F);
			*/
			fa = ::from_bit(pos(b, var0, n_vars),false) &&
					::from_bit(pos(b, var1, n_vars),false);
			r = fa && ::from_bit(pos(b, var2, n_vars),false);

		}
		else if (b == 1) {
			/*
			fa = bdd_ite(::from_bit(pos(b, var0, n_vars),true),
						 ::from_bit(pos(b, var1, n_vars),true),
						 bdd_handle::F);
			*/
			fa = ::from_bit(pos(b, var0, n_vars),true) &&
					::from_bit(pos(b, var1, n_vars),true);
			r = r && fa && ::from_bit(pos(b, var2, n_vars),true);
		}
		else {
			fa = full_adder( var0, var1, n_vars , b);

			r = r && bdd_ite(fa ,
				::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));

			/*
			set<int_t> sizes;
			bdd_size(r, sizes);
			int_t bsize = 0;
			int_t count = 0;
			for (auto elem : sizes)
			{	if (elem > bsize)
					bsize = elem;
				count++;
				//o::dbg() << elem << L" , ";
			}
			o::dbg() <<  L" BDD size for adder bit " << b-2 << L" : "
				  <<  bsize  << L" , "  << count << endl;
			*/
		}

		//bdd::gc();

	}

	/*
	set<int_t> sizes;
	bdd_size(r, sizes);
	int_t bsize = 0;
	int_t count = 0;
	for (auto elem : sizes)
	{	if (elem > bsize)
			bsize = elem;
		count++;
		//o::dbg() << elem << L" , ";
	}
	o::dbg() <<  L" BDD size for adder eq  : " <<  bsize  << L" , " \
		  << count << endl;
	*/
	bdd::gc();
 	return r;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// general multiplier

spbdd_handle tables::add_ite_carry(size_t var0, size_t var1, size_t n_vars,
		uint_t i, uint_t j) {

	static alumemo x;
	static map<alumemo, spbdd_handle>::const_iterator it;

	if ((it = carrymemo.find(x = { var0, var1, n_vars, bits, i, j })) !=
			carrymemo.end()) {
		//o::dbg() << L" [ memo carry]: " << i << L" -- " << j << endl;
		return it->second;
	}

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
			r = bdd_ite( bit,
					acc_i || carry_j,
					acc_i && carry_j
			);
		}
	}
	return carrymemo.emplace(x, r), r;
}

spbdd_handle tables::add_ite(size_t var0, size_t var1, size_t n_vars, uint_t i,
		uint_t j) {

	//o::dbg() << L" [ ADDITE : " << bits << L" ]: " << i << L" -- " << j << endl;
	static alumemo x;
	static map<alumemo, spbdd_handle>::const_iterator it;
	if ((it = addermemo.find(x = { var0, var1, n_vars, bits, i, j })) !=
			addermemo.end()) {
		//o::dbg() << L" [adder memo]: " << i << L" -- " << j << endl;
		return it->second;
	}

	spbdd_handle r;

	//extended precision support
	if (i - j == bits - 2) {
		r = add_ite_carry(var0, var1, n_vars,i-1,j);
	}
	//--

	//o::dbg() << L" [ ADDITE ]: " << i << L" -- " << j << endl;
	else if (i == 2 || j == 2) {

			r = ::from_bit(pos(j, var0, n_vars),true) &&
					::from_bit(pos(i, var1, n_vars),true);
		}
	else if (i == j) {
		/*
		return bdd_ite(add_ite(var0, var1, n_vars, i, j-1),
				   bdd_ite(::from_bit(pos(j, var0, n_vars),true),
						   ::from_bit(pos(2, var1, n_vars),false),
							bdd_handle::T),
  				   bdd_ite(::from_bit(pos(j, var0, n_vars),true),
  						   ::from_bit(pos(2, var1, n_vars),true) ,
  						   bdd_handle::F));
  		*/
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
								bdd_ite(carry_ij, bdd_handle::T, bdd_handle::F ),
								bdd_ite(carry_ij, bdd_handle::F, bdd_handle::T )),
						bdd_ite(acc_i ,
								bdd_ite(carry_ij, bdd_handle::F, bdd_handle::T ),
								bdd_ite(carry_ij, bdd_handle::T, bdd_handle::F ))
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

		//bdd::gc();

		//equality
		r = r && bdd_ite(acc_bit ,
				::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));

	}

	/*
	set<int_t> sizes;
	bdd_size(r, sizes);
	int_t bsize = 0;
	int_t count = 0;
	for (auto elem : sizes)
	{	if (elem > bsize)
			bsize = elem;
		count++;
		o::dbg() << elem << L" , ";
	}
	o::dbg() <<  L" BDD size for " << bits-2 << L" : " <<  bsize  << L" , "  << count << endl;
	*/
	//*sizes.end()
	bdd::gc();

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

		//bdd::gc();

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
	bdd::gc();

	return r;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

//shr for equality
spbdd_handle tables::shr(size_t var0, size_t n, size_t var2,
		size_t n_vars)  {

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

	return s;
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

				wcout << i*n_vars+j+1 << L"--" << perm1[i*n_vars+j]+1 << endl;

			}

		s = s^perm1;

		for(size_t i = 0; i < n; i++)
			s = s && ::from_bit(pos(i+2, var2, n_vars), false);

	} else {
		for(size_t i = 0; i < bits-2; i++)
		    	s = s && ::from_bit(pos(i+2, var2, n_vars), false);
	}

	return s;
}

//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
// bitwise operators
t_arith_op tables::get_bwop(lexeme l) {
	if (l == L"bw_and")
		return BITWAND;
	else if (l == L"bw_or")
		return BITWOR;
	else if (l == L"bw_xor")
			return BITWXOR;
	else if (l == L"bw_not")
		return BITWNOT;
	else return NOP;
}

// pairwise operators
t_arith_op tables::get_pwop(lexeme l) {
	if (l == L"pw_add")
		return ADD;
	else if (l == L"pw_mult")
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

// bdd var "tanslate"
spbdd_handle tables::perm_from_to(size_t from, size_t to, spbdd_handle in, size_t n_bits,
		size_t n_vars) {

	uints perm1;
	perm1 = perm_init(n_bits*n_vars);
	for (size_t i = 0; i < n_bits; i++) {
		for (size_t j = 0; j < n_vars; ++j) {
			if (j == from ) {
				//wcout << perm1[i*n_vars+j]  << L" ** " <<  perm1[i*n_vars+to] << endl;
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
	//::out(o::dbg(), s0)<<endl<<endl;
    //::out(o::dbg(), s1)<<endl<<endl;

	spbdd_handle x;
	switch (op) {
		case ADD : x = bdd_adder(s0, s1); break;
		case MULT: x = bdd_mult_dfs(s0, s1, bits-2,3); break;
		default  : break;
	}
	x = perm_bit_reverse( x, bits-2, n_vars);
	//::out(o::dbg(), x)<<endl<<endl;

	x = perm_from_to(2, out_varid, x, bits-2, n_vars);
	x = x && ::from_bit(pos(1, out_varid, n_vars),true) &&
			::from_bit(pos(0, out_varid, n_vars),false);

	return x;
}


// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// XXX: test support code

spbdd_handle tables::bdd_mult_test(size_t n_vars) {

	size_t n_args = n_vars;
	size_t out_arg = 2;

	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0, n_args, mknum(0));
	s0 = s0 || from_sym(0, n_args, mknum(1));
	s0 = s0 || from_sym(0, n_args, mknum(2));
	s0 = s0 || from_sym(0, n_args, mknum(3));
	s0 = s0 || from_sym(0, n_args, mknum(4));
	s0 = s0 || from_sym(0, n_args, mknum(5));
	s0 = s0 || from_sym(0, n_args, mknum(6));
	s0 = s0 || from_sym(0, n_args, mknum(7));
	s0 = s0 || from_sym(0, n_args, mknum(8));
	s0 = s0 || from_sym(0, n_args, mknum(9));
	s0 = s0 || from_sym(0, n_args, mknum(10));
	s0 = s0 || from_sym(0, n_args, mknum(11));
	s0 = s0 || from_sym(0, n_args, mknum(12));
	s0 = s0 || from_sym(0, n_args, mknum(13));
	s0 = s0 || from_sym(0, n_args, mknum(14));
	s0 = s0 || from_sym(0, n_args, mknum(15));
	s0 = s0 || from_sym(0, n_args, mknum(16));
	s0 = s0 || from_sym(0, n_args, mknum(17));
	s0 = s0 || from_sym(0, n_args, mknum(18));
	s0 = s0 || from_sym(0, n_args, mknum(19));
	s0 = s0 || from_sym(0, n_args, mknum(20));
	s0 = s0 || from_sym(0, n_args, mknum(21));
	s0 = s0 || from_sym(0, n_args, mknum(22));
	s0 = s0 || from_sym(0, n_args, mknum(23));
	s0 = s0 || from_sym(0, n_args, mknum(24));
	s0 = s0 || from_sym(0, n_args, mknum(25));
	s0 = s0 || from_sym(0, n_args, mknum(26));
	s0 = s0 || from_sym(0, n_args, mknum(27));
	s0 = s0 || from_sym(0, n_args, mknum(28));
	s0 = s0 || from_sym(0, n_args, mknum(29));
	s0 = s0 || from_sym(0, n_args, mknum(30));
	s0 = s0 || from_sym(0, n_args, mknum(31));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1, n_args, mknum(0));
	s1 = s1 || from_sym(1, n_args, mknum(1));
	s1 = s1 || from_sym(1, n_args, mknum(2));
	s1 = s1 || from_sym(1, n_args, mknum(3));
	s1 = s1 || from_sym(1, n_args, mknum(4));
	s1 = s1 || from_sym(1, n_args, mknum(5));
	s1 = s1 || from_sym(1, n_args, mknum(6));
	s1 = s1 || from_sym(1, n_args, mknum(7));
	s1 = s1 || from_sym(1, n_args, mknum(8));
	s1 = s1 || from_sym(1, n_args, mknum(9));
	s1 = s1 || from_sym(1, n_args, mknum(10));
	s1 = s1 || from_sym(1, n_args, mknum(11));
	s1 = s1 || from_sym(1, n_args, mknum(12));
	s1 = s1 || from_sym(1, n_args, mknum(13));
	s1 = s1 || from_sym(1, n_args, mknum(14));
	s1 = s1 || from_sym(1, n_args, mknum(15));
	s1 = s1 || from_sym(1, n_args, mknum(16));
	s1 = s1 || from_sym(1, n_args, mknum(17));
	s1 = s1 || from_sym(1, n_args, mknum(16));
	s1 = s1 || from_sym(1, n_args, mknum(19));
	s1 = s1 || from_sym(1, n_args, mknum(20));
	s1 = s1 || from_sym(1, n_args, mknum(21));
	s1 = s1 || from_sym(1, n_args, mknum(22));
	s1 = s1 || from_sym(1, n_args, mknum(23));
	s1 = s1 || from_sym(1, n_args, mknum(24));
	s1 = s1 || from_sym(1, n_args, mknum(25));
	s1 = s1 || from_sym(1, n_args, mknum(26));
	s1 = s1 || from_sym(1, n_args, mknum(27));
	s1 = s1 || from_sym(1, n_args, mknum(28));
	s1 = s1 || from_sym(1, n_args, mknum(29));
	s1 = s1 || from_sym(1, n_args, mknum(30));
	s1 = s1 || from_sym(1, n_args, mknum(31));


	//remove "type" bits
	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
	  for (size_t j = 0; j< n_args; ++j)
	    if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
		  else exvec.push_back(false);
	}
	s0 = s0 / exvec;
	s1 = s1 / exvec;

	//XXX: check need of gc here
	bdd::gc();

	//bit reverse
	uints perm1;
	perm1 = perm_init((bits-2)*n_args);
	for (size_t i = 0; i < (bits-2)*n_args; i++) {
		perm1[i] = ((bits-2-1-(i/n_args))*n_args) + i % n_args;
	}
	s0 = s0^perm1;
	s1 = s1^perm1;

	//XXX: check need of gc here
	bdd::gc();

	//wcout << L" ------------------- bdd mult  :\n";
	spbdd_handle test = bdd_mult_dfs(s0, s1, bits-2, n_args);

	//bit reverse and append type bits
	test = (test^perm1) && ::from_bit(pos(1, out_arg, n_args),true) &&
		::from_bit(pos(0, out_arg, n_args),false);

	return test;
}

spbdd_handle tables::bdd_add_test(size_t n_vars) {


	o::dbg() << L" ------------------- bdd adder  :\n";

	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0,3,mknum(2));
	s0 = s0 || from_sym(0,3,mknum(3));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1,3,mknum(16));
	s1 = s1 || from_sym(1,3,mknum(20));
	s1 = s1 || from_sym(1,3,mknum(24));
	s1 = s1 || from_sym(1,3,mknum(28));


	// remove "type" bits
	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
		for (size_t j = 0; j< n_vars; ++j)
			if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
				else exvec.push_back(false);
	}
	s0 = s0 / exvec;
	s1 = s1 / exvec;

	// bit reverse
	uints perm1;
	perm1 = perm_init((bits-2)*n_vars);
	for (size_t i = 0; i < (bits-2)*n_vars; i++) {
		perm1[i] = ((bits-2-1-(i/n_vars))*n_vars) + i % n_vars;
	}
	s0 = s0^perm1;
	s1 = s1^perm1;
	bdd::gc();

	spbdd_handle test = bdd_adder(s0,s1);

	test = test^perm1 && ::from_bit(pos(1, 2, n_vars),true) && ::from_bit(pos(0, 2, n_vars),false);

	return test;

}

spbdd_handle tables::bdd_test(size_t n_vars) {

	/*
	spbdd_handle s0 = bdd_handle::T;
	s0 =  from_sym( 0,  3, mknum(4));
	s0 = s0 || from_sym( 0,  3, mknum(5));
	s0 = s0 || from_sym( 0,  3, mknum(6));
	s0 = s0 || from_sym( 0,  3, mknum(7));
    //s0 = s0 || from_sym( 0,  3, mknum(1));
	o::dbg() << L" ------------------- S0 " << L":\n";
	::out(o::dbg(), s0)<<endl<<endl;

	//spbdd_handle s1 = bdd_handle::T;
	//s1 = from_sym( 0,  2, mknum(1));
	//s1 = s1 || from_sym( 0,  2, mknum(7));
	////s1 = s1 || from_sym( 0,  3, mknum(2));
	////s1 = s1 || from_sym( 0,  3, mknum(3));
	o::dbg() << L" ------------------- S1 " << L":\n";
    ::out(o::dbg(), s1)<<endl<<endl;

    // s0, s1
	// && intersection
    // || union
    //  % complemento
    // XOR
    //spbdd_handle r = s0 && s1;
    //spbdd_handle r = s0 || s1;
    //spbdd_handle r = s0 % s1;
    //spbdd_handle r = bdd_handle::T % s0;
    //spbdd_handle r = bdd_xor(s0,s1);

	spbdd_handle s2 = bdd_handle::T;
	s2 = from_sym( 0,  3, mknum(3));
	s2 = s2 || from_sym( 0,  3, mknum(7));
	//s2 = s2 || from_sym( 0,  3, mknum(2));

	o::dbg() << L" ------------------- S2 " << ::bdd_root(s2) << L" :\n";
	::out(o::dbg(), s2)<<endl<<endl;

	spbdd_handle r = s0 && s2;
	o::dbg() << L" ------------------- &&:union " << bdd_nvars(r )<< L" :\n";
	::out(o::dbg(), r)<<endl<<endl;

	//spbdd_handle test = bdd_ite_var(pos(4, 0, 3), s0 && s2 &&
	//	 ::from_bit(pos(4, 0, 3), 1), ::from_bit(pos(4, 0, 3), 0));
	//spbdd_handle test = ::from_bit(3,true);
	*/

	// -------------------------------------------------------------------

	/*
	// TEST: a = {6}, b = {4,5,6,7}, out = {4,6}
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  3, mknum(6));

	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym( 1,  3, mknum(4));
	s1 =  s1 || from_sym( 1,  3, mknum(5));
	s1 =  s1 || from_sym( 1,  3, mknum(6));
	s1 =  s1 || from_sym( 1,  3, mknum(7));
	*/

	/*
	// TEST:  a = {5,2}, b = {3} out = {1,2}
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  3, mknum(5));
	s0 = s0 || from_sym( 0,  3, mknum(2));

	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym( 1,  3, mknum(3));
	*/

	/*
	// TEST:  a = {4}, b = {3} out = {0}
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  3, mknum(4));
	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym( 1,  3, mknum(3));
	*/

	/*
	// TEST:  a = {4}, b = {3} out = {0}
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  3, mknum(4));
	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym( 1,  3, mknum(3));
	 */

	/*
	// TEST:  a = {2}, b = {1} out = {0}
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  3, mknum(2));
	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym( 1,  3, mknum(1));
    */

	/*
	// TEST:  a = {2,3}, b = {1,2} out = {0,1,2}
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  3, mknum(2));
	s0 = s0 ||from_sym( 0,  3, mknum(3));
	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym( 1,  3, mknum(1));
	s1 =  s1 || from_sym( 1,  3, mknum(2));
	*/

	/*
	// TEST:  a = {2,3}, b = {1,5} out = {0,1}
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  3, mknum(2));
	s0 = s0 ||from_sym( 0,  3, mknum(3));
	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym( 1,  3, mknum(1));
	s1 =  s1 || from_sym( 1,  3, mknum(5));
	*/

	/*
	// TEST:  a = {4,7}, b = {4,7} out = {4,7}
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  3, mknum(4));
	s0 = s0 ||from_sym( 0,  3, mknum(7));
	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym( 1,  3, mknum(4));
	s1 =  s1 || from_sym( 1,  3, mknum(7));
	*/

	/*
	// TEST:  a = {4,5,6,7}, b = {2,3,4,5,6,7} out = {0,1,2,3,4,5,6,7}
	spbdd_handle s0 = bdd_handle::F;
	//s0 = s0 || from_sym( 0,  3, mknum(4));
	s0 = s0 || from_sym(0,3,mknum(5));
	s0 = s0 || from_sym(0,3,mknum(6));
	s0 = s0 || from_sym(0,3,mknum(7));

	spbdd_handle s1 = bdd_handle::F;
	//s1 = s1 || from_sym(1,3,mknum(1));
	s1 = s1 || from_sym(1,3,mknum(2));
	//s1 = s1 || from_sym(1,3,mknum(4));
	s1 = s1 || from_sym(1,3,mknum(5));
	s1 = s1 || from_sym(1,3,mknum(6));
	s1 = s1 || from_sym(1,3,mknum(7));
	*/

	/*
	// TEST:  a = { ... }, b = { ... } out = { ...}
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0,3,mknum(1));
	s0 = s0 || from_sym(0,3,mknum(3));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1,3,mknum(3));
	s1 = s1 || from_sym(1,3,mknum(0));
	//s1 = s1 || from_sym(1,3,mknum(5));
	//s1 = s1 || from_sym(1,3,mknum(5));
	//s1 = s1 || from_sym(1,3,mknum(6));
	//s1 = s1 || from_sym(1,3,mknum(7));

	// remove "type" bits
	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
	  for (size_t j = 0; j< n_vars; ++j)
	    if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
		  else exvec.push_back(false);
	}
	s0 = s0 / exvec;
	s1 = s1 / exvec;
	bdd::gc();

	// ***
	// call to bitwise over bdds handlers...
	// ***

	//o::dbg() << L" ------------------- bitwise_and  :\n";
	//spbdd_handle test = bdd_bitwise_and(s0,s1) && ::from_bit(pos(1, var2, n_vars),true) && ::from_bit(pos(0, var2, n_vars),false);

	o::dbg() << L" ------------------- bitwise_xor  :\n";
	spbdd_handle test = bdd_bitwise_xor(s0,s1) && ::from_bit(pos(1, 2, n_vars),true) && ::from_bit(pos(0, 2, n_vars),false);


	return test;
	*/

	//size_t n_args = n_vars;
	//spbdd_handle s0 = bdd_handle::F;
	/*
	s0 = s0 || from_sym(2, n_args, mknum(0));
	s0 = s0 || from_sym(2, n_args, mknum(6));
	s0 = s0 || from_sym(2, n_args, mknum(12));
	s0 = s0 || from_sym(2, n_args, mknum(18));
	s0 = s0 || from_sym(2, n_args, mknum(24));
	s0 = s0 || from_sym(2, n_args, mknum(30));
	s0 = s0 || from_sym(2, n_args, mknum(36));
	s0 = s0 || from_sym(2, n_args, mknum(42));
	s0 = s0 || from_sym(2, n_args, mknum(48));
	s0 = s0 || from_sym(2, n_args, mknum(54));
	s0 = s0 || from_sym(2, n_args, mknum(60));
	s0 = s0 || from_sym(2, n_args, mknum(66));
	s0 = s0 || from_sym(2, n_args, mknum(72));
	s0 = s0 || from_sym(2, n_args, mknum(78));
	s0 = s0 || from_sym(2, n_args, mknum(84));
	s0 = s0 || from_sym(2, n_args, mknum(90));
	*/
	/*
	spbdd_handle s1 = bdd_handle::F;
	for (int i = 2; i < 256 ; i++) {
		for (int j = 2; j < 256 ; j++) {
			s1 = s1 || from_sym(2, n_args, mknum(i*j));
		}
	}
	*/
	/*
	for (int i = 1; i < 256 ; i++) {
			s0 = s0 || from_sym(2, n_args, mknum(6*i+1));
			s0 = s0 || from_sym(2, n_args, mknum(6*i-1));
	}
	*/


/*
	spbdd_handle s0 = bdd_handle::F;
	s0 = from_sym( 0,  1, mknum(0));
	s0 = s0 || from_sym( 0,  1, mknum(1));
	s0 = s0 || from_sym( 0,  1, mknum(2));

	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym(0,  1, mknum(0));
	//s1 =  s1 || from_sym(0,  1, mknum(3));

	//s1 =  s1 || from_sym( 1,  3, mknum(5));
	//s1 =  s1 || from_sym( 1,  3, mknum(6));
	//s1 =  s1 || from_sym( 1,  3, mknum(7));

	// remove "type" bits
	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
		if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
				else exvec.push_back(false);
	}
	s0 = s0 / exvec;
	s1 = s1 / exvec;
*/

	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym( 0,  2, mknum(1));
	s0 = s0 || from_sym( 1,  2, mknum(0));

	s0 = s0 || from_sym( 0,  2, mknum(1));
	s0 = s0 || from_sym( 1,  2, mknum(1));

	s0 = s0 || from_sym( 0,  2, mknum(1));
	s0 = s0 || from_sym( 1,  2, mknum(0)); //not necessary


	spbdd_handle s1 = bdd_handle::F;
	s1 =  from_sym(0,  1, mknum(0));
	//s1 =  s1 || from_sym(0,  1, mknum(3));
	//s1 =  s1 || from_sym( 1,  3, mknum(5));
	//s1 =  s1 || from_sym( 1,  3, mknum(6));
	//s1 =  s1 || from_sym( 1,  3, mknum(7));
	ex_typebits(s0, n_vars);
	ex_typebits(s1, n_vars);

	o::dbg() << L" ------------------- " << ::bdd_root(s1) << L" :\n";
	::out(wcout, s1)<<endl<<endl;

	spbdd_handle test = bdd_not(s1) || s0 ;

	o::dbg() << L" ------------------- " << ::bdd_root(test) << L" :\n";
	::out(wcout, test)<<endl<<endl;

	return s0;
}
