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

typedef tuple<size_t, size_t, size_t, int_t> akmemo;
map<akmemo, spbdd_handle> alumemo;

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

extern uints perm_init(size_t n);

// ----------------------------------------------------------------------------

bool tables::isalu_handler(const term& t, alt& a, spbdd_handle &leq) {

	DBG(wcout << "ALU handler ... " << endl;)
	spbdd_handle q;

	switch (t.alu_op) {
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
				q = add_var_const_eq_const(bit_0, a.varslen, t[1], t[2]);
			}
			else if (t[0] < 0 && t[1] >= 0 && t[2] < 0 ) {
				//VAR + CONST = VAR
				size_t bit_0 = a.vm.at(t[0]);
				size_t bit_2 = a.vm.at(t[2]);
				q = add_var_const_eq_var(bit_0, bit_2, a.varslen, t[1]);
			}
			else if (t[0] < 0 && t[1] < 0 && t[2] < 2) {
				//all VARS
				size_t bit_0 = a.vm.at(t[0]);
				size_t bit_1 = a.vm.at(t[1]);
				size_t bit_2 = a.vm.at(t[2]);
				q = add_var(bit_0, bit_1, bit_2, a.varslen);
			}
			*/

			//all types of addition hanlder by add_var
			//its working for
			//var + var = var
			//var + var = const
			//var + const = const
			//BUT not for:
			//const + var = const
			//var + const = var

			size_t args = 3;
			q = add_var(0, 1, 2, args);

			int nconsts = 0;

			for (size_t i = 0; i< args; ++i) {
				if (t[i] >= 0) {
					spbdd_handle aux = from_sym(i, args, t[i]);
					q = q && aux;
					nconsts++;
				}
			}

			bools exvec;
			for (size_t i = 0; i < bits; ++i) {
				for (size_t j = 0; j< args; ++j) {
					if (t[j] >= 0)
						exvec.push_back(true);
					else
						exvec.push_back(false);
				}
			}
			q = q/exvec;

			uints perm = perm_init(args*bits);
			for (size_t i = 0; i < bits; ++i) {
				if (t[0] < 0)
					perm[i*args] = perm[i*args]-(i*nconsts) ;
				if (t[1] < 0)
					 perm[i*args+1] = perm[i*args+1]-(i*nconsts) ;
				if (t[2] < 0)
					perm[i*args+2] = perm[i*args+2]-(i*nconsts) ;

			}
			q = q^perm;
		} break;

		case SHR:
		{
			DBG(wcout << "SHR handler ... " << endl;)
			q = bdd_handle::T;
		} break;

		case SHL:
		{
			DBG(wcout << "SHL handler ... " << endl;)
			size_t bit_0 = a.vm.at(t[0]);
			size_t bit_2 = a.vm.at(t[2]);
			assert(mknum(1) == t[1] && "only << 1 supported");
			q = shl(bit_0, 1, bit_2, a.varslen);
		} break;

		case MULT:
		{
			DBG(wcout << "MULT handler ... " << endl;)
			q = bdd_handle::T;
		} break;;

	}

	//&&
	#ifdef REPORT
	wcout << L"q:\n  ";
	::out(wcout, q)<<endl<<endl;
	#endif

	leq = leq && q;

	#ifdef REPORT
	wcout << L"leq(add):\n  ";
	::out(wcout, a.eq)<<endl<<endl;
	#endif

	return true;

}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------


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

spbdd_handle tables::add_var(size_t var0, size_t var1, size_t var2,
		size_t n_vars) {

	/*
	//carry test
	for (size_t b = 2; b != bits; ++b) {
		spbdd_handle carry = bdd_handle::F;
		carry = full_addder_carry(var0, var1, n_vars, b, carry);
		wcout << L" ---------------------:\ncarry " << b <<  L": ";
				::out(wcout, carry)<<endl<<endl;
	}
	*/

	spbdd_handle r = bdd_handle::T;

	for (size_t b = 0; b != bits; ++b) {
		spbdd_handle fa = full_adder( var0, var1, n_vars , b);
		r = r && bdd_ite(fa ,
				::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));
	}
 	return r;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

//shr for a const
spbdd_handle tables::shr_test(size_t var0, int_t n1, size_t var2,
		size_t n_vars)  {

	spbdd_handle n = bdd_handle::T;
	n = from_sym(var0, n_vars, n1);

	bools exvec;
	for (size_t i = 0; i < 2*(bits-3); i++)
		exvec.push_back(false);
	exvec.push_back(true);
	exvec.push_back(true);
	spbdd_handle ex0 = n/exvec;


	uints perm1;
	perm1 = perm_init(2*bits);
	for (size_t i = 0; i < 2*(bits-3); i++) {
		perm1[i] = perm1[i]+2;
		wcout << perm1[i] << L" --- " << perm1[i]+2 << L"\n";
	}

	spbdd_handle shr = ex0^perm1 && ::from_bit(pos(bits-1, var0, n_vars), false);
	return shr;
}
// ----------------------------------------------------------------------------

//shl for an equality
spbdd_handle tables::shl(size_t var0, int_t n1, size_t var2,
		size_t n_vars)  {

	//shl
	spbdd_handle n = bdd_handle::T;
	n = n && from_sym_eq(var0, var2, n_vars);

	bools exvec;
	for (size_t i = 0; i < (2*bits); i++)
		exvec.push_back(false);
	exvec[2*(bits-3)] = true;
	//for (size_t i = 0; i < (2*bits); i++) wcout << L" --- " << exvec[i]; wcout << endl;

    uints perm1;
 	perm1 = perm_init(2*bits);
    // for (size_t i = 0; i < (2*bits); i++) wcout << L" --- " << perm1[i]; wcout << endl;
    for (size_t i = 0; i < (bits-3); i++) {
     	perm1[2*i] = perm1[2*i]+2;
    }
    //for (size_t i = 0; i < (2*bits); i++) wcout << L" --- " << perm1[i]; wcout << endl;


    n = n/exvec;

    spbdd_handle shl = n^perm1 &&
    		::from_bit(pos(bits-1, var0, n_vars), false) &&
    		::from_bit(pos(2, var2, n_vars), false);

	return shl;

}

//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

// BACKUP DECLARATIONS:
/*
	spbdd_handle from_bit_or(uint_t b, bool v, uint_t c) const;
	spbdd_handle from_add1(uint_t b0, uint_t b1, bool v, uint_t c) const;
	spbdd_handle add_const(int_t c0, int_t c1, size_t arg, size_t args,
		size_t bit) const;
	spbdd_handle add_var_const_eq_const(size_t var, size_t n_vars,  int_t n0,
		int_t n1) const;
	spbdd_handle add_var_const_eq_var(size_t var0, size_t var2, size_t n_vars,
		int_t n1) const;
	spbdd_handle add_one(size_t arg1, size_t arg2, size_t args, size_t bits,
		size_t bit, spbdd_handle r);
	spbdd_handle add_one(size_t arg1, size_t arg2, size_t args);
	spbdd_handle full_addder_one_carry(size_t var0, size_t n_vars, uint_t b, spbdd_handle r) const;
	spbdd_handle full_adder_one(size_t var0, size_t n_vars, uint_t b) const;
*/

/*
spbdd_handle tables::permute_test(size_t var0, int_t n1, size_t var2, size_t n_vars, alt& a)  {

	spbdd_handle r = bdd_handle::T;
	spbdd_handle n = bdd_handle::T;

	n = from_sym(var0, n_vars, n1);// && from_sym(var2, n_vars, mknum(7));
	wcout << L" ---------------------:\n";
	::out(wcout, n)<<endl<<endl;
	wcout << L" *** BITS = " << bits << L":\n";

	uints perm0  = perm_init(bits);
	spbdd_handle nop = n^perm0;
	wcout << L" ---------------------:\n nop(N)-post_perm:\n";
    ::out(wcout, nop)<<endl<<endl;

    return r;
}
*/


/*
spbdd_handle tables::test(size_t var0, int_t n1, size_t var2, size_t n_vars, alt& a)  {
		spbdd_handle r = bdd_handle::T;
	r = r || from_sym( 1,  2, mknum(3));
	r = r || from_sym( 0,  2, mknum(3));
	r = r %  from_sym( 1,  2, mknum(2));
	r = r %  from_sym( 0,  2, mknum(2));
	wcout << L" ---------------------:" << (n1 >> 2) << L"\n r: ";
			::out(wcout, r)<<endl<<endl;
	wcout << L"################################# >\n";

 	return r;

}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

spbdd_handle tables::from_bit_or(uint_t b, bool v, uint_t c) const {
	wcout << "bit or \n";

	if (c < 2) return v ? ::from_bit(b,true) : ::from_bit(b,false);
	return v ? bdd_handle::T : ::from_bit(b,true);
}


spbdd_handle tables::add_var_const_eq_const(size_t var, size_t n_vars,
											int_t n0, int_t n1) const {
	//static skmemo x;
	//static map<skmemo, spbdd_handle>::const_iterator it;
	//if ((it = smemo.find(x = { i, pos, args, bits })) != smemo.end())
	//	return it->second;
	spbdd_handle r = bdd_handle::T;
	for (size_t b = 0; b != bits; ++b)
		r = r && from_bit_or(pos(b, var, n_vars), n0 & (1 << b), b);

	//return smemo.emplace(x, r), r;
	return r;
}

// ----------------------------------------------------------------------------
// c is used to identify 2 LSB encoding type
// bitwise OR handler: VAR | NUM = VAR
spbdd_handle tables::from_add1(uint_t b0, uint_t b1, bool v, uint_t c) const {

	if (c < 2) {
		return bdd_ite(::from_bit(b0,true), ::from_bit(b1,true), ::from_bit(b1,false));
	}

	return v ? ::from_bit(b1, true) : bdd_ite(
			::from_bit(b0, true), ::from_bit(b1, true), ::from_bit(b1, false));

}

spbdd_handle tables::add_var_const_eq_var(size_t var0, size_t var2,
		size_t n_vars,  int_t n1) const {


	spbdd_handle r = bdd_handle::T;

	for (size_t b = 0; b != bits; ++b) {

		r = r && from_add1(pos(b, var0, n_vars), pos(b, var2, n_vars),
				n1 & (1 << b), b);

		#ifdef REPORT
		wcout << L" ---------------------:\n";
			::out(wcout, r)<<endl<<endl;
		#endif
	}

	return r;

}

// ----------------------------------------------------------------------------
*/
