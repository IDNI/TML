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
			//XXX: temporary location to test adder over bdds
			//q = bdd_add_test(args);

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
			//for (size_t i = 0; i < (3*bits); i++)
			//	wcout << L" --- " << perm[i]; wcout << endl;

			uints perm2 = get_perm(t, a.vm, a.varslen);
			//for (size_t i = 0; i < (3*bits); i++)
			//	wcout << L" --- " << perm2[i]; wcout << endl;

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

			size_t args = 3; //t.size();
			size_t n_vars = 0;

			if (args == 3) {

				q = mul_var_eq(0,1,2,3);

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

				//q = bdd_test(args);
				//n_vars = args;
			}

			/*
			//XXX: hook for extended precition
			//XXX wont run, needs update in parser like ?x0:?x1
			else if (args == 4) {
				q = mul_var_eq_ext(0,1,2,3,args);
				n_vars = args;

				//XXX: temporay hook to test mult over bdds
				//varmap extension:

				//for (size_t n = 0; n != bits-2+1; ++n)
				//	a.vm.emplace( -1*a.varslen , a.varslen++);
				//q = bdd_mult_test(args);
				//n_vars = args + bits - 2 +1;

			}

			int nconsts = 0;
			for (size_t i = 0; i< args; ++i)
				if (t[i] >= 0) {
					spbdd_handle aux = from_sym(i, n_vars, t[i]);
					q = q && aux;
					nconsts++;
				}

			bools exvec;
			for (size_t i = 0; i < bits; ++i) {
				for (size_t j = 0; j< args; ++j)
					if (t[j] >= 0) exvec.push_back(true);
					else exvec.push_back(false);

				for (size_t j = 0; j< n_vars - args; ++j)
					exvec.push_back(true);
			}
			q = q/exvec;


			//for (size_t n = 0; n < bits - 2; ++n) {
			//	a.vm.erase(-1*a.varslen);
			//	a.varslen--;
			//}


			bools exvec;
			for (size_t i = 0; i < bits; ++i) {
				for (size_t j = 0; j< args; ++j)
					if (t[j] >= 0) exvec.push_back(true);
					else exvec.push_back(false);
			}

			q = q/exvec;
			//FIXME: memory fault, invalid read
			uints perm2 = get_perm_ext(t, a.vm, a.varslen);
			q = q^perm2;
			*/

		} break;

		default:
			break;

	}

	leq = leq && q;

	return true;

}

// ----------------------------------------------------------------------------

spbdd_handle tables::bdd_mult_test(size_t n_vars) {

	wcout << L" ------------------- BITS  :" << bits << L"\n";

	//return bdd_handle::F;

	size_t n_accs = bits - 2 + 1;
	size_t n_args = n_accs + n_vars;

	/*
	// TEST : ok
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0, n_args ,mknum(2));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1, n_args,mknum(2));
	s1 = s1 || from_sym(1, n_args,mknum(1));
	*/

	/*
	// TEST : ok
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0, n_args ,mknum(1));
	s0 = s0 || from_sym(0, n_args ,mknum(2));
	s0 = s0 || from_sym(0, n_args ,mknum(3));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1, n_args,mknum(2));
	*/

	/*
	// TEST : ok
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0, n_args ,mknum(1));
	s0 = s0 || from_sym(0, n_args ,mknum(2));
	s0 = s0 || from_sym(0, n_args ,mknum(3));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1, n_args,mknum(1));
	*/

	/*
	// TEST : ok
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0, n_args, mknum(0));
	s0 = s0 || from_sym(0, n_args, mknum(1));
	s0 = s0 || from_sym(0, n_args, mknum(2));
	s0 = s0 || from_sym(0, n_args, mknum(3));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1, n_args, mknum(3));
	*/

	/*
	// TEST : ok
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0, n_args, mknum(1));
	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1, n_args, mknum(1));
	s1 = s1 || from_sym(1, n_args, mknum(2));
	 */

	/*
	// TEST : ok
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0, n_args, mknum(1));
	s0 = s0 || from_sym(0, n_args, mknum(2));
	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1, n_args, mknum(1));
	s1 = s1 || from_sym(1, n_args, mknum(2));
	s1 = s1 || from_sym(1, n_args, mknum(3));
	*/



	// TEST : FAIL
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0, n_args, mknum(5));
	s0 = s0 || from_sym(0, n_args, mknum(6));
	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1, n_args, mknum(1));
	s1 = s1 || from_sym(1, n_args, mknum(7));
	s1 = s1 || from_sym(1, n_args, mknum(3));

	spbdd_handle *accs = new spbdd_handle[n_accs] ;

	for (size_t i = 0; i < n_accs; ++i) {
		accs[i] = from_sym(n_vars + i, n_args ,mknum(0));
	}

	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
	  for (size_t j = 0; j< n_args; ++j)
	    if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
		  else exvec.push_back(false);
	}
	s0 = s0 / exvec;
	s1 = s1 / exvec;
	//acc = acc / exvec;
	for (size_t i = 0; i < n_accs; ++i) {
		accs[i] = accs[i] / exvec;
	}

	bdd::gc();

	wcout << L" ------------------- bdd mult  :\n";

	uints perm1;
	perm1 = perm_init((bits-2)*n_args);
	for (size_t i = 0; i < (bits-2)*n_args; i++) {
		//wcout << L" perminit " << perm1[i] << L"\n";
		perm1[i] = ((bits-2-1-(i/n_args))*n_args) + i % n_args;
		//wcout << L" newperm " << perm1[i] << L"\n";
	}
	s0 = s0^perm1;
	s1 = s1^perm1;
	//acc = acc^perm1;
	for (size_t i = 0; i < n_accs; ++i) {
		accs[i] = accs[i]^perm1;
	}

	wcout << L" ------------------- A " << ::bdd_root(s0) << L" :\n";
	::out(wcout, s0)<<endl<<endl;
	wcout << L" ------------------- B " << ::bdd_root(s1) << L" :\n";
	::out(wcout, s1)<<endl<<endl;

	bdd::gc();

	spbdd_handle test = bdd_mult_dfs(s0,s1,accs, bits-2, n_args);

	wcout << L" ------------------- testout " << ::bdd_root(test) << L" :\n";
	::out(wcout, test)<<endl<<endl;

	test = test^perm1 && ::from_bit(pos(1, 3, n_args),true) &&
			::from_bit(pos(0, 3, n_args),false);

	delete [] accs;
	return test;

}

spbdd_handle tables::bdd_add_test(size_t n_vars) {


	wcout << L" ------------------- bdd adder  :\n";

	// TEST
	spbdd_handle s0 = bdd_handle::T;
	//s0 = s0 || from_sym(0,3,mknum(3));
	//s0 = s0 || from_sym(0,3,mknum(2));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1,3,mknum(3));
	s1 = s1 || from_sym(1,3,mknum(2));
	s1 = s1 || from_sym(1,3,mknum(1));
	s1 = s1 || from_sym(1,3,mknum(0));

	/*
	// TEST
	spbdd_handle s0 = bdd_handle::F;
	s0 = s0 || from_sym(0,3,mknum(7));
	s0 = s0 || from_sym(0,3,mknum(6));
	s0 = s0 || from_sym(0,3,mknum(5));
	s0 = s0 || from_sym(0,3,mknum(4));

	spbdd_handle s1 = bdd_handle::F;
	s1 = s1 || from_sym(1,3,mknum(3));
	s1 = s1 || from_sym(1,3,mknum(2));
    */

	// remove "type" bits
	bools exvec;
	for (size_t i = 0; i < bits; ++i) {
		for (size_t j = 0; j< n_vars; ++j)
			if (i == bits - 2 || i == bits - 1 ) exvec.push_back(true);
				else exvec.push_back(false);
	}
	s0 = s0 / exvec;
	s1 = s1 / exvec;

	// invert endianess
	uints perm1;
	perm1 = perm_init((bits-2)*n_vars);
	for (size_t i = 0; i < (bits-2)*n_vars; i++) {
		//wcout << L" perminit " << perm1[i] << L"\n";
		perm1[i] = ((bits-2-1-(i/n_vars))*n_vars) + i % n_vars;
		//wcout << L" newperm " << perm1[i] << L"\n";
	}
	s0 = s0^perm1;
	s1 = s1^perm1;
	bdd::gc();

	wcout << L" ------------------- A " << ::bdd_root(s0) << L" :\n";
	::out(wcout, s0)<<endl<<endl;
	wcout << L" ------------------- B " << ::bdd_root(s1) << L" :\n";
	::out(wcout, s1)<<endl<<endl;

	spbdd_handle test = bdd_adder(s0,s1);

	wcout << L" ------------------- testout " << ::bdd_root(test) << L" :\n";
	::out(wcout, test)<<endl<<endl;

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

	//wcout << L" ------------------- bitwise_and  :\n";
	//spbdd_handle test = bdd_bitwise_and(s0,s1) && ::from_bit(pos(1, var2, n_vars),true) && ::from_bit(pos(0, var2, n_vars),false);

	wcout << L" ------------------- bitwise_xor  :\n";
	spbdd_handle test = bdd_bitwise_xor(s0,s1) && ::from_bit(pos(1, 2, n_vars),true) && ::from_bit(pos(0, 2, n_vars),false);

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
			wcout <<  L" BDD size for adder bit " << b-2 << L" : "
				  <<  bsize  << L" , "  << count << endl;
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
	wcout <<  L" BDD size for adder eq  : " <<  bsize  << L" , " \
		  << count << endl;

 	return r;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

spbdd_handle tables::full_addder_carry_shift(size_t var0, size_t var1,
		size_t n_vars, uint_t b, uint_t s, spbdd_handle r) const {

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

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
spbdd_handle tables::add_ite_carry(size_t var0, size_t var1, size_t n_vars,
		uint_t i, uint_t j) {

	static alumemo x;
	static map<alumemo, spbdd_handle>::const_iterator it;

	if ((it = carrymemo.find(x = { var0, var1, n_vars, bits, i, j })) !=
			carrymemo.end()) {
		//wcout << L" [ memo carry]: " << i << L" -- " << j << endl;
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

	//wcout << L" [ ADDITE : " << bits << L" ]: " << i << L" -- " << j << endl;
	static alumemo x;
	static map<alumemo, spbdd_handle>::const_iterator it;
	if ((it = addermemo.find(x = { var0, var1, n_vars, bits, i, j })) !=
			addermemo.end()) {
		//wcout << L" [adder memo]: " << i << L" -- " << j << endl;
		return it->second;
	}

	spbdd_handle r;

	//extended precision support
	if (i - j == bits - 2) {
		r = add_ite_carry(var0, var1, n_vars,i-1,j);
	}
	//--

	//wcout << L" [ ADDITE ]: " << i << L" -- " << j << endl;
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

// ----------------------------------------------------------------------------

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

		bdd::gc();

		//wcout << L" -------------------ACC BIT " << b << L":\n";
		//	::out(wcout, acc_bit)<<endl<<endl;

		//equality
		r = r && bdd_ite(acc_bit ,
				::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));

		wcout << L" ------------------- BIT " << b << L" of " << bits-1 << L" done\n";

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

spbdd_handle tables::mul_var_eq_ext(size_t var0, size_t var1, size_t var2, size_t var3,
			size_t n_vars) {

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

		bdd::gc();

		//equality
		r = r && bdd_ite(acc_bit ,
				::from_bit(pos(b, var2, n_vars), true),
				::from_bit(pos(b, var2, n_vars), false));
	}

	for (size_t b = 2; b < bits; ++b) {

		spbdd_handle acc_bit = bdd_handle::F;
		acc_bit = add_ite(var0, var1, n_vars, bits + (b-2) , bits-1);
		bdd::gc();

		//equality
		r = r && bdd_ite(acc_bit ,
				::from_bit(pos(b, var3, n_vars), true),
				::from_bit(pos(b, var3, n_vars), false));
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
