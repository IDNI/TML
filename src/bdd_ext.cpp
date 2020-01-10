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
#include <cassert>
#include <algorithm>
#include "bdd.h"
#include "output.h"
using namespace std;

//------------------------------------------------------------------------------
//auxiliar funcions
int_t bdd_root(cr_spbdd_handle x) {
	return (bdd::var(x->b));
}

void bdd_size(cr_spbdd_handle x,  std::set<int_t>& s) {
	bdd::bdd_sz_abs(x->b, s);
}

//------------------------------------------------------------------------------
spbdd_handle bdd_xor(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_xor(x->b,y->b));
}

//------------------------------------------------------------------------------
//over bdd bitwise operators
spbdd_handle bdd_bitwise_and(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bitwiseAND(x->b,y->b));
}

spbdd_handle bdd_bitwise_xor(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bitwiseXOR(x->b,y->b));
}

spbdd_handle bdd_adder(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::ADDER(x->b,y->b, false, 0));
}

spbdd_handle bdd_mult_dfs(cr_spbdd_handle x, cr_spbdd_handle y, spbdd_handle *z,
	size_t bits, size_t n_vars ) {

	//bdds
	int_t *z_aux = new int_t[bits];
	for (size_t i = 0 ; i < bits; i++) {
		z_aux[i] = z[i]->b;
	}
	spbdd_handle out =
		bdd_handle::get(bdd::MULT_DFS(x->b,y->b, z_aux , 0, bits, n_vars, true));

	delete[] z_aux;
	return out;
}


// ----------------------------------------------------------------------------

void bdd::bdd_sz_abs(int_t x, set<int_t>& s) {
	if (!s.emplace(abs(x)).second) return;
	bdd b = get(x);
	bdd_sz_abs(b.h, s), bdd_sz_abs(b.l, s);
}

int_t bdd::bdd_xor(int_t x, int_t y) {
	return bdd_and( bdd_or(x,y), -bdd_and(x,y));
}

//XXX: intial proof of concept implementation, can be significantly complacted
int_t bdd::bitwiseAND(int_t a_in, int_t b_in) {

	  bdd a = get(a_in), b = get(b_in);
	  int_t c = 0;
	  uint_t pos = 0;

	  wcout << L" -- a.v = " << a.v << L", b.v = " <<  b.v  << L"\n";

	  //XXX: assumes var a < var b
	  if (a.v > b.v + 1 && b.v != 0) {
	    a.h = a_in, a.l = a_in;
	    pos = b.v+1;
	  }
	  else if (a.v + 2 < b.v && a.v != 0 ) {
	    b.h = b_in, b.l = b_in;
	    pos = a.v + 2;
	  } else if (a.v != 0)
	    pos = a.v+2;
	  else
	    pos = b.v + 1;

	  wcout << L" ------------------- pos = " << pos << L"\n";

	  // ---------------------------------------------------------------------------

	  if (a_in == T && b_in == T)
		  c = T;
	  else if (a_in == F || b_in == F)
		  c = F;
	  else if (a_in == T ) {
	    //(b.h,b.l) = 0,1 | 1,0 | 0,x | x,0 | 1,x | x,1 | x,x
	    if (b.h == F && b.l == T)
	      c = add(pos, F, T);
	    else if (b.h == T && b.l == F)
	      c = T;
	    else if (b.h == F)
	      c = add(pos, F /*b.h, a.h && b.h*/,  bitwiseAND(T, b.l) );
	    else if (b.h == T)
   	      c = add(pos, T /*b.h, a.h && b.h*/ , bitwiseAND(T, b.l));
	    else if (b.l == F)
	      c = add(pos, bitwiseAND(T, b.h), bitwiseAND(T, b.h));
	    else if (b.l == T)
	      c = T; // === add(pos, T ()   , bitwiseAND(T, b.l));
	    else
	      c = add(pos, bitwiseAND(T, b.h), bitwiseAND(T, b.l));

	  } else if (b_in == T) {
  	     //XXX: swap?, idem above
		if (a.h == F && a.l == T)
		  c = add(pos, F, T);
		else if (a.h == T && a.l == F)
		  c = T;
		else if (a.h == F)
		  c = add(pos, F, bitwiseAND(a.l, T));
		else if (a.h == T)
		  c = add(pos, T , bitwiseAND(a.l, T));
		else if (a.l == F)
		  c = add(pos, bitwiseAND(a.h, T), bitwiseAND(a.h, T)); // (Verif OK)
		else if (a.l == T)
		  c = T;
		else
		  c = add(pos, bitwiseAND(a.h, T), bitwiseAND(a.l, T));

	  }
	  // ---------------------------------------------------------------------------
	  // ---------------------------------------------------------------------------
	  // H = 0,0 | 0,1 | 1,0 | 0,x | x,0
	  else if (a.h == F || b.h == F) {
	    // H = 0,0
	    if (a.h == F && b.h == F && a.l != T && b.l != T)
	      c = add(pos, F, bitwiseAND(a.l, b.l));
	    else if (a.h == F && b.h == F)// && a.l == T && b.l == T)
	      c = F;
	    // H = 0,1 | 0,x
	    else if (a.h == F && b.l == F ) //b.h == T || b.h == x
	      c = add(pos, F, bitwiseAND(a.l,  b.h  ));
	    else if (a.h == F) //b.l != 0 && b.h != 0
	      c = add(pos, F, bdd_or( bitwiseAND(a.l,  b.l ), bitwiseAND(a.l,  b.h ) ) );
	    // H = 1,0 | x,0
	    else if (b.h == F && a.l == F ) //a.h == T || a.h == x
	      c = add(pos, F, bitwiseAND( a.h , b.l ));
	    else if (b.h == F) //a.l != 0 && a.h != 0
	      c = add(pos, F, bdd_or( bitwiseAND(a.l,  b.l ), bitwiseAND(a.h,  b.l ) ) );
	  }
	  // ---------------------------------------------------------------------------
	  // H = 1,1 | 1,x | x,1 | x,x
	  else {
	    // H = 1,1
	    if (a.h == T && b.h == T) {
	      if (a.l == F && b.l == F)
	        c = add(pos, T, F);
	      else if(a.l == F)
	    	c = add(pos, T, bitwiseAND(T, b.l));
		  else if(b.l == F)
			c = add(pos, T, bitwiseAND(a.l, T));
		  else
			c = add(pos, T, bitwiseAND(a.l, a.l));
	    }

		// H = 1,x
	    else if (a.h == T) {
	      if (a.l == F && b.l == F)
	    	c = add(pos, bitwiseAND( T , b.h ), F);
	      else if (a.l == F && b.l == T)
	    	c = add(pos, bitwiseAND( T , b.h ), T /*bitwiseAND( T , b.l )*/);
	      else if (a.l == F)
	    	c = add(pos, bitwiseAND( T , b.h ), bitwiseAND( T , b.l ));
	      else //a.l = x, b.l = 0 | 1 | x
			c = add(pos, bitwiseAND( T , b.h ),
					bdd_or(bitwiseAND(a.l , b.h), bitwiseAND(a.l , b.l)));
	      	  	  	  //a.h , b.l ??
	    }

	    // H = x,1
	    else if (b.h == T) {
	      // L = 0,0 | 1,0 | x,0 | 0,x | 1,x | x,x

	      if (a.l == F && b.l == F)
	        c = add(pos, bitwiseAND( a.h , T ), F);
	      else if (a.l == T && b.l == F)
	    	c = add(pos, bitwiseAND( a.h , T ), T /*bitwiseAND(a.l, T)*/);
	      else if (b.l == F ) // L = x,0
	    	c = add(pos, bitwiseAND( a.h , T ), bitwiseAND( a.l , T ));
	      else if (a.l == F)
	        c = add(pos,
	      	   		bitwiseAND( a.h , T ),
					bitwiseAND( a.h , b.l ) );
	      else if (a.l == T)
	    	c = add(pos,
	    			bitwiseAND( a.h , T ),
					bitwiseAND( T , b.l ));
	      else
	    	c = add(pos,
	    			bitwiseAND( a.h , T ),
	    			bdd_or(bitwiseAND(a.h , b.l), bitwiseAND(a.l , b.l)));
	      	  	  	//a.l , b.h ??
	    }

	    // H = x,x
	    else {
	      //if (a.l == F && b.l == F)
	      //  c = add(pos, bitwiseAND( a.h , b.h ), F);
	      if (a.l == F) // b.l =  0, 1 , x
	        c = add(pos, bitwiseAND( a.h , b.h ), bitwiseAND( a.h , b.l ));
	      else if (b.l == F)
	    	c = add(pos, bitwiseAND( a.h , b.h ), bitwiseAND( a.l , b.h ));

	      else if (a.l == T || b.l == T)
	    	c = add(pos,
	    	        bitwiseAND( a.h , b.h ),
					bdd_or(bitwiseAND( a.h , b.l ) , bitwiseAND( a.h , b.l )));

	      else //(a.l == x & b.l == x)
	        c = add(pos, bitwiseAND(a.h,  b.h ),

	        		bdd_or ( bdd_or(bitwiseAND(a.h,  b.l ), bitwiseAND(a.l,  b.h )) ,
							 				 bitwiseAND(a.l,  b.l )));
	    }
	  }

	  return c;

}

int_t bdd::bitwiseXOR(int_t a_in, int_t b_in) {

	bdd a = get(a_in), b = get(b_in);
	int_t c = 0;
	int_t pos = 0;

	wcout << L" -- a.v = " << a.v << L", b.v = " <<  b.v  << L"\n";

	//XXX: assumes var a < var b
	if (a.v > b.v + 1 && b.v != 0) {
		a.h = a_in, a.l = a_in;
		pos = b.v+1;
	}
	else if (a.v + 2 < b.v && a.v != 0 ) {
		b.h = b_in, b.l = b_in;
		pos = a.v + 2;
	} else if (a.v != 0)
		pos = a.v+2;
	else
		pos = b.v + 1;

	//wcout << L" ------------------- pos = " << pos << L"\n";
	// ---------------------------------------------------------------------------

	if (a_in == T && b_in == T)
		c = T;
	else if (a_in == F || b_in == F)
		c = F;
	else
		c = add(pos,
				bdd_or(bitwiseXOR(a.h, b.l), bitwiseXOR(a.l, b.h)),
				bdd_or(bitwiseXOR(a.h, b.h), bitwiseXOR(a.l, b.l)));
	return c;
}

// ----------------------------------------------------------------------------

// For adder:
// const size_t n_args = 3;

int_t bdd::ADDER(int_t a_in, int_t b_in, bool carry, size_t bit) {

	bdd a = get(a_in), b = get(b_in);
	int_t c = 0;
	int_t pos = 0;

	//wcout << L" -- a.v = " << a.v << L", b.v = " <<  b.v  << L"\n";

	pos = (bit + 1) * 3;
	if (a.v > pos) a.h = a_in, a.l = a_in;
	if (b.v > pos) b.h = b_in, b.l = b_in;
	wcout << L" ------------------- pos = " << pos << L"\n";

	// ---------------------------------------------------------------------------

	if (a_in == T && b_in == T)
		c = T;
	else if (a_in == F || b_in == F)
		c = F;
	else {
		if (carry == false)
			c = add(pos,
					bdd_or(ADDER(a.h, b.l, false, bit+1), ADDER(a.l, b.h, false, bit+1)),
					bdd_or(ADDER(a.h, b.h, true,  bit+1), ADDER(a.l, b.l, false, bit+1)));
		else
			c = add(pos,
					bdd_or(ADDER(a.h, b.h, true, bit+1), ADDER(a.l, b.l, false, bit+1)),
					bdd_or(ADDER(a.h, b.l, true, bit+1), ADDER(a.l, b.h, true,  bit+1)));
	}

	return c;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// Over bdds MULT support
// ----------------------------------------------------------------------------

extern uints perm_init(size_t n);

template<typename T> struct veccmp {
	bool operator()(const vector<T>& x, const vector<T>& y) const{
		if (x.size() != y.size()) return x.size() < y.size();
		return x < y;
	}
};
extern map<uints, unordered_map<int_t, int_t>, veccmp<uint_t>> memos_perm;


//does addition over bdd b and acc[depth] and stores ouput in acc[depth+1]
int_t bdd::ADDER_IDX(int_t a_in, int_t b_in, bool carry, size_t bit, size_t depth,
	size_t n_args) {

	bdd a = get(a_in), b = get(b_in);
	int_t c = 0;
	int_t pos = 0;

	//wcout << L" -- a.v = " << a.v << L", b.v = " <<  b.v  << L"\n";
	pos = bit * n_args + 5 /*accs_offset*/ + depth  + 1;
	if (a.v > pos) {a.h = a_in, a.l = a_in;}
	if (b.v > pos) {b.h = b_in, b.l = b_in;}
	//wcout << L" ------------------- pos = " << pos << L"\n";

	// --------------------------------------------------------------------------

	if (a_in == T && b_in == T)
		c = T;
	else if (a_in == F || b_in == F)
		c = F;
	else {
		if (carry == false)
			c = add(pos,
					bdd_or(ADDER_IDX(a.h, b.l, false, bit+1, depth, n_args),
								 ADDER_IDX(a.l, b.h, false, bit+1, depth, n_args)),
					bdd_or(ADDER_IDX(a.h, b.h, true, bit+1, depth, n_args ),
								 ADDER_IDX(a.l, b.l, false, bit+1, depth, n_args)));
		else
			c = add(pos,
					bdd_or(ADDER_IDX(a.h, b.h, true, bit+1, depth, n_args),
								 ADDER_IDX(a.l, b.l, false, bit+1, depth, n_args)),
					bdd_or(ADDER_IDX(a.h, b.l, true, bit+1, depth, n_args),
								 ADDER_IDX(a.l, b.h, true, bit+1, depth, n_args )));
	}
	return c;

}

// ----------------------------------------------------------------------------

int_t bdd::ADDER_ACCS(int_t b_in, int_t *accs, size_t depth, size_t bits, size_t n_args) {

	/*uints perm1;

	size_t tbits = n_args*bits;

	perm1 = perm_init(tbits);

	//wcout << L"[ADDER_ACCS] " << depth << L" " << bits << L" " << n_args << L"\n";

	size_t base = 4; // = number of arguments of the alt

	//int_t
	//--

	bools exvec;
	for (size_t i = 0; i < tbits; ++i) {
		if (i == base + depth)
			exvec.push_back(true);
		else exvec.push_back(false);
	}

	int_t acc_aux = bdd_permute_ex(accs[depth],exvec ,perm1);
	//return acc_false_aux;

	for (size_t i = 1; n_args*i+base+depth < tbits ; i++) {
		wcout << perm1[n_args*i+base + depth] << L" --- " << perm1[n_args*i+base+depth]-n_args << L"\n";
		perm1[n_args*i+base+depth] = perm1[n_args*i+base+depth]-n_args;
	}

	acc_aux = bdd_permute(acc_aux, perm1, memos_perm[perm1]);

	size_t pos_z = n_args * (bits-1) + base + depth + 1;
	int_t aux_bit = add(pos_z,F,T);
	acc_aux = bdd_and(acc_aux, aux_bit);

	//accs[depth] = acc_aux;


	//int_t c = acc_false_aux;

	//bdd acc_false = get(acc_false_aux);
	//bdd acc_true  = get(ADDER(b_in, acc_false_aux, false));

	*/

	int_t acc_aux = SHR(accs[depth], depth, bits, n_args);

	//XXX: optimization possible is to alredy keep acc array shifted
	//accs[depth] = acc_aux;

	//int_t c = ADDER_IDX(b_in, acc_aux, false, depth, depth+1);
	int_t c = ADDER_IDX(b_in, acc_aux, false, 0, depth, n_args);

	return c;
}


/*
int_t bdd::ADDER_3x(int_t b_in, int_t *accs, size_t depth, size_t bits, size_t n_args) {
	int_t acc_aux = SHR(accs[depth], depth, bits, n_args);
	//int_t c = ADDER_IDX(b_in, acc_aux, false, depth, depth+1);
	int_t c = ADDER_IDX(b_in, acc_aux, false, 0, depth, n_args);

	return c;
}
*/
// ----------------------------------------------------------------------------

int_t bdd::COPY(int_t a_in) {
	 if (a_in == T) return T;
	 else if (a_in == F) return F;
	 bdd a = get(a_in);
	 int_t pos = a.v + 1;
 	 int_t c = add(pos, COPY(a.h) , COPY(a.l));
 	 return c;
}

int_t bdd::SHR(int_t a_in, size_t depth, size_t bits, size_t n_args) {

	uints perm1;
	size_t tbits = n_args*bits;
	size_t base = 4; // = number of arguments of the alt

	perm1 = perm_init(tbits);

	bools exvec;
	for (size_t i = 0; i < tbits; ++i) {
		if (i == base + depth)
			exvec.push_back(true);
		else exvec.push_back(false);
	}
	int_t acc_aux = bdd_permute_ex(a_in, exvec ,perm1);

	for (size_t i = 1; n_args*i+base+depth < tbits ; i++) {
		//wcout << perm1[n_args*i+base + depth] << L" --- " << perm1[n_args*i+base+depth]-n_args << L"\n";
		perm1[n_args*i+base+depth] = perm1[n_args*i+base+depth]-n_args;
	}
	acc_aux = bdd_permute(acc_aux, perm1, memos_perm[perm1]);

	size_t pos_z = n_args * (bits-1) + base + depth + 1;
	int_t aux_bit = add(pos_z,F,T);
	acc_aux = bdd_and(acc_aux, aux_bit);

	return acc_aux;
}

int_t bdd::MULT_DFS(int_t a_in, int_t b_in, int_t *accs, size_t depth, size_t bits,
	size_t n_args, bool bit_acc) {

	int_t c;
	int_t pos = 4 + n_args * depth;

	wcout << L"[MULT_DFS] " << depth << L" " << bits << L" " << n_args <<  L" " << bit_acc << L"\n";
	wcout << L" ------------------- pos = " << pos << L"\n";

	if (a_in == F || b_in == F || bit_acc == false) {
		wcout << L"[MULT_DFS] " << depth << L" " << bits << L" " << n_args <<  L" " << bit_acc << L" = F \n";
		return  F;
	}
	else if (a_in == T && bit_acc == true && depth == bits)// && b_in == T)
		{
		wcout << L"[MULT_DFS] " << depth << L" " << bits << L" " << n_args <<  L" " << bit_acc << L" = T \n";
		return T;
	}
	//XXX else if (a_in == T && bit_acc == false)// && b_in == T)

	else  {

		bdd a = get(a_in);
		if (a.v > pos) {a.h = a_in, a.l = a_in;}

		//XXX avoid addition and recursive in case a.h = f
		accs[depth+1] = ADDER_ACCS(b_in, accs, depth, bits, n_args);

		//wcout << L"##[ ACC TRUE " << depth+1 << L"]:" << endl;
		//out(wcout, accs[depth+1]);
		//wcout <<endl<<endl;

		bdd aux_acc_true = get(accs[depth+1]);
		int_t aux_acc_true_h = add(aux_acc_true.v, aux_acc_true.h, F) ;
		int_t aux_acc_true_l = add(aux_acc_true.v, F, aux_acc_true.l) ;

		accs[depth+1] = aux_acc_true_h;

		//wcout << L"##[ ACC TRUE check" << depth+1 << L"]:" << endl;
		//out(wcout, accs[depth+1]);
		//wcout <<endl<<endl;


		int_t aux00  = MULT_DFS(a.h, b_in, accs, depth+1, bits, n_args, aux_acc_true.h != F || aux_acc_true.v > n_args);

		//bdd aux_acc_true_h = aux_acc_true.h;
		accs[depth+1] = aux_acc_true_l;

		wcout << L"##[ ACC TRUE check" << depth+1 << L"]:" << endl;
		out(wcout, accs[depth+1]);
		wcout <<endl<<endl;

		int_t aux10  = MULT_DFS(a.h, b_in, accs, depth+1, bits, n_args, aux_acc_true.l != F || aux_acc_true.v > n_args);

		//acc_false, just copy of depth, since shr has already been applier for acc_true
		accs[depth+1] = COPY(accs[depth]);
		accs[depth+1] = SHR(accs[depth+1], depth+1, bits, n_args);

		wcout << L"##[ ACC FALSE" << depth+1 << L"]:" << endl;
		out(wcout, accs[depth+1]);
		wcout <<endl<<endl;


		bdd aux_acc_false = get(accs[depth+1]);
		int_t aux01  = MULT_DFS(a.l, b_in, accs, depth+1, bits, n_args, aux_acc_false.h != F || aux_acc_false.v > n_args);
		int_t aux11  = MULT_DFS(a.l, b_in, accs, depth+1, bits, n_args, aux_acc_false.l != F || aux_acc_false.v > n_args);

		c = add(pos, bdd_or(aux00, aux01), bdd_or(aux10, aux11));

		wcout << L"[MULT_DFS] " << depth << L" " << bits << L" " << n_args <<  L" " << bit_acc << L" = \n";
		out(wcout, c);
		wcout <<endl<<endl;

		return c;

	}
}

// ----------------------------------------------------------------------------
/*
c = add(pos,

		 bdd_or( MULT(a.h, b_in,  acc_true.h, bits ), MULT(a.l, b_in, acc_false.h, bits) ) ,

	   bdd_or( MULT(a.h, b_in, acc_true.l, bits), MULT(a.l, b_in, acc_false.l, bits) ) );
*/

// ----------------------------------------------------------------------------
