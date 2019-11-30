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

			//all types of addition hanlder by add_var
			//XXX not working for ?x + ?x = 2

			size_t args = 3;
			q = add_var_eq(0, 1, 2, args);

			int nconsts = 0;

			for (size_t i = 0; i< args; ++i)
				if (t[i] >= 0) {
					spbdd_handle aux = from_sym(i, args, t[i]);
					q = q && aux;
					nconsts++;
				}

			bools exvec;
			for (size_t i = 0; i < bits; ++i) {
				for (size_t j = 0; j< args; ++j)
					if (t[j] >= 0) exvec.push_back(true);
					else exvec.push_back(false);
			}
			q = q/exvec;

			//uints perm = perm_init(args*bits);
			//for (size_t i = 0; i < bits; ++i) {
			//	if (t[0] < 0) perm[i*args] = perm[i*args]-(i*nconsts) ;
			//	if (t[1] < 0) perm[i*args+1] = perm[i*args+1]-(i*nconsts) ;
			//	if (t[2] < 0) perm[i*args+2] = perm[i*args+2]-(i*nconsts) ;
			//}
			//for (size_t i = 0; i < (3*bits); i++) wcout << L" --- " << perm[i]; wcout << endl;

			uints perm2 = get_perm(t, a.vm, a.varslen);
			//for (size_t i = 0; i < (3*bits); i++) wcout << L" --- " << perm2[i]; wcout << endl;

			q = q^perm2;

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

			//uints perm1 = get_perm(t, a.vm, a.varslen);
			//for (size_t i = 0; i < (3*bits); i++) wcout << L" --- " << perm1[i]; wcout << endl;

			size_t args = 3;
			//q = mul_var_eq(0,1,2,3);

			q = bdd_test(0,1,2,args);


			int nconsts = 0;
			for (size_t i = 0; i< args; ++i)
				if (t[i] >= 0) {
					spbdd_handle aux = from_sym(i, args, t[i]);
					q = q && aux;
					nconsts++;
				}
			bools exvec;
			for (size_t i = 0; i < bits; ++i) {
				for (size_t j = 0; j< args; ++j)
					if (t[j] >= 0) exvec.push_back(true);
					else exvec.push_back(false);
			}
			q = q/exvec;
			uints perm2 = get_perm(t, a.vm, a.varslen);
			q = q^perm2;

		} break;

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
spbdd_handle tables::bdd_test(size_t var0, size_t var1, size_t var2,
			size_t n_vars) {

	/*
	spbdd_handle s0 = bdd_handle::T;
	s0 =  from_sym( 0,  3, mknum(4));
	s0 = s0 || from_sym( 0,  3, mknum(5));
	s0 = s0 || from_sym( 0,  3, mknum(6));
	s0 = s0 || from_sym( 0,  3, mknum(7));
    //s0 = s0 || from_sym( 0,  3, mknum(1));
	wcout << L" ------------------- S0 " << L":\n";
	::out(wcout, s0)<<endl<<endl;

	//spbdd_handle s1 = bdd_handle::T;
	//s1 = from_sym( 0,  2, mknum(1));
	//s1 = s1 || from_sym( 0,  2, mknum(7));
	////s1 = s1 || from_sym( 0,  3, mknum(2));
	////s1 = s1 || from_sym( 0,  3, mknum(3));
	wcout << L" ------------------- S1 " << L":\n";
    ::out(wcout, s1)<<endl<<endl;

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

	wcout << L" ------------------- S2 " << ::bdd_root(s2) << L" :\n";
	::out(wcout, s2)<<endl<<endl;

	spbdd_handle r = s0 && s2;
	wcout << L" ------------------- &&:union " << bdd_nvars(r )<< L" :\n";
	::out(wcout, r)<<endl<<endl;

	//spbdd_handle test = bdd_ite_var(pos(4, 0, 3), s0 && s2 && ::from_bit(pos(4, 0, 3), 1), ::from_bit(pos(4, 0, 3), 0));
	//spbdd_handle test = ::from_bit(3,true);
	*/

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


/*
	spbdd_handle s0 = bdd_handle::T;

	spbdd_handle s1 = bdd_handle::F;
	//s1 = s1 || from_sym(1,3,mknum(3));
	s1 = s1 || from_sym(1,3,mknum(4));
	s1 = s1 || from_sym(1,3,mknum(5));
	//s1 = s1 || from_sym(1,3,mknum(6));
	//s1 = s1 || from_sym(1,3,mknum(7));
*/

	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
	  for (size_t j = 0; j< n_vars; ++j)
	    if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
		  else exvec.push_back(false);
	}
	s0 = s0 / exvec;
	wcout << L" ------------------- S0 " << ::bdd_root(s0) << L" :\n";
	::out(wcout, s0)<<endl<<endl;

	s1 = s1 / exvec;
	wcout << L" ------------------- S1 " << ::bdd_root(s1) << L" :\n";
	::out(wcout, s1)<<endl<<endl;

	bdd::gc();
	spbdd_handle test = bdd_bitwise_and(s0,s1) && ::from_bit(pos(1, var2, n_vars),true) && ::from_bit(pos(0, var2, n_vars),false);

	// ***
	// call to bitwise_and over bdds ...
	// ***

	wcout << L" ------------------- bitwise_and  :\n";
	::out(wcout, test)<<endl<<endl;

	return test;
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
			fa = ::from_bit(pos(b, var0, n_vars),false) && ::from_bit(pos(b, var1, n_vars),false);
			r = fa && ::from_bit(pos(b, var2, n_vars),false);

		}
		else if (b == 1) {
			/*
			fa = bdd_ite(::from_bit(pos(b, var0, n_vars),true),
						 ::from_bit(pos(b, var1, n_vars),true),
						 bdd_handle::F);
			*/
			fa = ::from_bit(pos(b, var0, n_vars),true) && ::from_bit(pos(b, var1, n_vars),true);
			r = r && fa && ::from_bit(pos(b, var2, n_vars),true);
		}
		else {
			fa = full_adder( var0, var1, n_vars , b);

			r = r && bdd_ite(fa ,
				::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));

			set<int_t> sizes;
			bdd_size(r, sizes);
			int_t bsize = 0;
			int_t count = 0;
			for (auto elem : sizes)
			{	if (elem > bsize)
					bsize = elem;
				count++;
				//wcout << elem << L" , ";
			}
			wcout <<  L" BDD size for adder bit " << b-2 << L" : " <<  bsize  << L" , "  << count << endl;


		}

		//wcout << L" ---------------------:\nr " << L": ";
		//								::out(wcout, r)<<endl<<endl;
		bdd::gc();

	}

	set<int_t> sizes;
	bdd_size(r, sizes);
	int_t bsize = 0;
	int_t count = 0;
	for (auto elem : sizes)
	{	if (elem > bsize)
			bsize = elem;
		count++;
		//wcout << elem << L" , ";
	}
	wcout <<  L" BDD size for adder eq  : " <<  bsize  << L" , "  << count << endl;

 	return r;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

spbdd_handle tables::full_addder_carry_shift(size_t var0, size_t var1, size_t n_vars,
		uint_t b, uint_t s, spbdd_handle r) const {

	if (b == 1) return bdd_handle::F;

	return bdd_ite( full_addder_carry_shift(var0, var1, n_vars, b-1, s, r),
					bdd_ite( ::from_bit(pos(b, var0, n_vars),true),
							 bdd_handle::T,
							 b - s > 1 ? ::from_bit(pos(b - s, var1, n_vars),true) : bdd_handle::F),
					bdd_ite( ::from_bit(pos(b, var0, n_vars),true),
							 b - s > 1 ? ::from_bit(pos(b - s, var1, n_vars),true) : bdd_handle::F,
							 bdd_handle::F));
}


spbdd_handle tables::full_adder_shift(size_t var0, size_t var1, size_t n_vars,
		uint_t b, uint_t s) const {

	if (b == 2) return ::from_bit( pos(b, var0, n_vars),true)
								&& ::from_bit( pos(b, var1, n_vars),true);


	else if (b == 2)
		return bdd_ite(::from_bit(pos(b, var0, n_vars),true),
				 	   b - s > 1 ? ::from_bit(pos(b - s, var1, n_vars),false) : bdd_handle::T,
				 	   b - s > 1 ? ::from_bit(pos(b - s, var1, n_vars),true) : bdd_handle::F);

	spbdd_handle carry = bdd_handle::F;
	carry = full_addder_carry_shift(var0, var1, n_vars, b-1, s, carry);

	return bdd_ite(
			carry,
			bdd_ite(::from_bit(pos(b, var0, n_vars),true),
					b - s > 1 ? ::from_bit(pos(b - s, var1, n_vars),true) : bdd_handle::T ,
					b - s > 1 ? ::from_bit(pos(b - s, var1, n_vars),false) : bdd_handle::F),
			bdd_ite(::from_bit(pos(b, var0, n_vars),true),
					b - s > 1 ? ::from_bit( pos(b - s, var1, n_vars),false) : bdd_handle::T,
					b - s > 1 ? ::from_bit( pos(b - s, var1, n_vars),true) : bdd_handle::F)
			);
}

/*
spbdd_handle tables::adder_shift(size_t var0, size_t var1, size_t n_vars, uint_t s ) {


	spbdd_handle r = bdd_handle::T;

	//s shift
	for (size_t = s; s != bits; ++s) {

		wcout << L" ----------------var0---:\n" << b << L" -> " <<  pos(b, var0, n_vars) <<  L" -< " << s << endl  ;
		wcout << L" ----------------var1---:\n" << b << L" -> " <<  pos(b, var1, n_vars) <<  L" -< " << s << endl  ;

		spbdd_handle fa = full_adder_shift( var1, var1, n_vars , b, s);

		wcout << L" -------------------FA_SHIFT :\n";
					::out(wcout, fa)<<endl<<endl;

	}
 	return r;
}
*/

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
/*
spbdd_handle tables::add_ite_carry(size_t var0, size_t var1, size_t n_vars, uint_t i, uint_t j) {

	if (i == 2 || j == 2) {
		wcout << L" add_ite_carry - base ----------------: " << i << L" -- " << j << endl;
		return ::from_bit(pos(j, var0, n_vars),true) && ::from_bit(pos(i, var1, n_vars),true);
	}

	spbdd_handle carry = bdd_handle::T;

	if (i-1 == j) {
		wcout << L" add_ite_carry - i-1==j ----------------: " << i << L" -- " << j << endl;
		carry = add_ite(var0, var1, n_vars, i-1, j-1) &&
						::from_bit(pos(j, var0, n_vars),true) &&
						::from_bit(pos(i-j+1, var1, n_vars),true);

		//wcout << L" -------------------BIT A:\n";
		//			::out(wcout, ::from_bit(pos(j, var0, n_vars),true))<<endl<<endl;
		//wcout << L" -------------------BIT B:\n";
		// 			::out(wcout, ::from_bit(pos(i-j+1, var1, n_vars),true))<<endl<<endl;
		wcout << L" add_ite_carry - i-1==j ----------------: " << i << L" -- " << j << endl;
		wcout << L" -------------------carry DIAG *** :\n";
							::out(wcout, carry)<<endl<<endl;

	}
	else {
		wcout << L" add_ite_carry - else ----------------: " << i << L" -- " << j << endl;
		carry = add_ite_carry(var0, var1, n_vars, i-1, j) &&
						::from_bit(pos(j, var0, n_vars),true) &&
						::from_bit(pos(i-j+1, var1, n_vars),true);

		//wcout << L" -------------------BIT A:\n";
		//			::out(wcout, ::from_bit(pos(j, var0, n_vars),true))<<endl<<endl;
		//wcout << L" -------------------BIT B:\n";
		//			::out(wcout, ::from_bit(pos(i-j+1, var1, n_vars),true))<<endl<<endl;
		wcout << L" add_ite_carry - else ----------------: " << i << L" -- " << j << endl;
		wcout << L" -------------------carry HORIZ *** :\n";
										::out(wcout, carry)<<endl<<endl;


	}
	return(carry);
}

spbdd_handle tables::add_ite(size_t var0, size_t var1, size_t n_vars, uint_t i, uint_t j) {


	if (i == 2 || j == 2) {
		wcout << L" add_ite - base ----------------: " << i << L" -- " << j << endl;
		return ::from_bit(pos(j, var0, n_vars),true) && ::from_bit(pos(i, var1, n_vars),true);

	}


	spbdd_handle carry = bdd_handle::T;

	if (i-1 == j) {
		wcout << L" add_ite - i-1==j ----------------: " << i << L" -- " << j << endl;
		carry = add_ite(var0, var1, n_vars, i-1, j-1) &&
						::from_bit(pos(j, var0, n_vars),true) &&
						::from_bit(pos(i-j+1, var1, n_vars),true);


		//wcout << L" -------------------BIT A:\n";
		//			::out(wcout, ::from_bit(pos(j, var0, n_vars),true))<<endl<<endl;
		//wcout << L" -------------------BIT B:\n";
		// 			::out(wcout, ::from_bit(pos(i-j+1, var1, n_vars),true))<<endl<<endl;
		wcout << L" add_ite - i-1==j ----------------: " << i << L" -- " << j << endl;
		wcout << L" -------------------carry DIAG:\n";
					::out(wcout, carry)<<endl<<endl;

	}
	else {
		wcout << L" add_ite - else ----------------: " << i << L" -- " << j << endl;
		carry = add_ite_carry(var0, var1, n_vars, i-1, j) &&
						::from_bit(pos(j, var0, n_vars),true) &&
						::from_bit(pos(i-j+1, var1, n_vars),true);

		wcout << L" -------------------BIT A:\n";
					::out(wcout, ::from_bit(pos(j, var0, n_vars),true))<<endl<<endl;
		wcout << L" -------------------BIT B:\n";
					::out(wcout, ::from_bit(pos(i-j+1, var1, n_vars),true))<<endl<<endl;
		wcout << L" add_ite - else ----------------: " << i << L" -- " << j << endl;
		wcout << L" -------------------carry HORIZ:\n";
					::out(wcout, carry)<<endl<<endl;


	}



	//uint_t
	return bdd_ite( carry,

				    bdd_ite( add_ite(var0, var1, n_vars, i, j-1),
						     bdd_ite(::from_bit(pos(j, var0, n_vars),true),
						    		 ::from_bit(pos(i-j+2, var1, n_vars),true),
									 bdd_handle::F),
							 bdd_ite(::from_bit(pos(j, var0, n_vars),true),
							  	     ::from_bit(pos(i-j+2, var1, n_vars),false),
									 bdd_handle::T)
							),

					bdd_ite( add_ite(var0, var1, n_vars, i, j-1) ,
							 bdd_ite(::from_bit(pos(j, var0, n_vars),true),
							  	     ::from_bit(pos(i-j+2, var1, n_vars),false),
									 bdd_handle::T),
						     bdd_ite(::from_bit(pos(j, var0, n_vars),true),
							  	     ::from_bit(pos(i-j+2, var1, n_vars),true),
									 bdd_handle::F)

							)
					);
	}

spbdd_handle tables::add_ite_init(size_t var0, size_t var1, size_t n_vars, uint_t i, uint_t j) {


	if (i == 2 || j == 2) {
			wcout << L" - base ----------------: " << i << L" -- " << j << endl;

			return ::from_bit(pos(j, var0, n_vars),true) && ::from_bit(pos(i, var1, n_vars),true);

		}

	wcout << L" i == j ----------------: " << i << L" -- " << j << endl;


	return bdd_ite(add_ite(var0, var1, n_vars, i, j-1),
				   bdd_ite(::from_bit(pos(j, var0, n_vars),true),
						   ::from_bit(pos(2, var1, n_vars),false),
							bdd_handle::T),
  				   bdd_ite(::from_bit(pos(j, var0, n_vars),true),
  						   ::from_bit(pos(2, var1, n_vars),true) ,
  						   bdd_handle::F));

}

*/

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
spbdd_handle tables::add_ite_carry(size_t var0, size_t var1, size_t n_vars, uint_t i, uint_t j) {

	//wcout << L" [ CARRY ]: " << i << L" -- " << j << endl;

	spbdd_handle acc_i = add_ite(var0, var1, n_vars, i, j-1);
	spbdd_handle bit = ::from_bit(pos(j, var0, n_vars),true) && ::from_bit(pos(i-j+2, var1, n_vars),true);

	if (i == j) {
		return acc_i && bit;
	}

	spbdd_handle carry_j = add_ite_carry(var0, var1, n_vars,i-1,j);
	return bdd_ite( bit,
					acc_i || carry_j,
					acc_i && carry_j
			);
}

spbdd_handle tables::add_ite(size_t var0, size_t var1, size_t n_vars, uint_t i, uint_t j) {

	//wcout << L" [ ADDITE ]: " << i << L" -- " << j << endl;
	if (i == 2 || j == 2) {

			return ::from_bit(pos(j, var0, n_vars),true) && ::from_bit(pos(i, var1, n_vars),true);
		}
	if (i == j) {
		/*
		return bdd_ite(add_ite(var0, var1, n_vars, i, j-1),
				   bdd_ite(::from_bit(pos(j, var0, n_vars),true),
						   ::from_bit(pos(2, var1, n_vars),false),
							bdd_handle::T),
  				   bdd_ite(::from_bit(pos(j, var0, n_vars),true),
  						   ::from_bit(pos(2, var1, n_vars),true) ,
  						   bdd_handle::F));
  		*/
		spbdd_handle bit = ::from_bit(pos(j, var0, n_vars),true) && ::from_bit(pos(i-j+2, var1, n_vars),true);
		spbdd_handle acc_i = add_ite(var0, var1, n_vars, i, j-1);
		return (bdd_xor(bit, acc_i));

	}
	if (i != j) {

		spbdd_handle bit = ::from_bit(pos(j, var0, n_vars),true) && ::from_bit(pos(i-j+2, var1, n_vars),true);
		spbdd_handle acc_i = add_ite(var0, var1, n_vars, i, j-1);
		spbdd_handle carry_ij = add_ite_carry(var0, var1, n_vars,i-1,j);

		spbdd_handle bout =  bdd_ite( bit ,
						bdd_ite(acc_i , bdd_ite(carry_ij, bdd_handle::T, bdd_handle::F ), bdd_ite(carry_ij, bdd_handle::F, bdd_handle::T )),
						bdd_ite(acc_i , bdd_ite(carry_ij, bdd_handle::F, bdd_handle::T ), bdd_ite(carry_ij, bdd_handle::T, bdd_handle::F ))
					);

		return bout;
	}
}

// ----------------------------------------------------------------------------

spbdd_handle tables::mul_var_eq(size_t var0, size_t var1, size_t var2,
			size_t n_vars) {


	spbdd_handle r = bdd_handle::T;
	r = r && ::from_bit(pos(0, var0, n_vars),false) && ::from_bit(pos(0, var1, n_vars),false) && ::from_bit(pos(0, var2, n_vars),false);
	r = r && ::from_bit(pos(1, var0, n_vars),true) && ::from_bit(pos(1, var1, n_vars),true) && ::from_bit(pos(1, var2, n_vars),true);

	for (size_t b = 2; b < bits; ++b) {

		spbdd_handle acc_bit = bdd_handle::F;
		acc_bit = add_ite(var0, var1, n_vars, b, b);

		bdd::gc();

		//wcout << L" -------------------ACC BIT " << b << L":\n";
		//	::out(wcout, acc_bit)<<endl<<endl;

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
		wcout << elem << L" , ";
	}
	wcout <<  L" BDD size for " << bits-2 << L" : " <<  bsize  << L" , "  << count << endl;
	*/
	//*sizes.end()

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
