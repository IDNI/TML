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


spbdd_handle bdd_xor (cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_xor(x->b,y->b));
}

int_t bdd_root(cr_spbdd_handle x) {
	return (bdd::var(x->b));
}

spbdd_handle bdd_bitwise_and(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bitwiseAND(x->b,y->b));
}

// ----------------------------------------------------------------------------
int_t bdd::bdd_xor(int_t x, int_t y) {
	return bdd_and( bdd_or(x,y), -bdd_and(x,y));
}

// ----------------------------------------------------------------------------

int_t bdd::bitwiseAND(int_t a_in, int_t b_in) {

	  bdd a = get(a_in), b = get(b_in);
	  int_t c = 0;
	  uint_t pos = 0;

	  //wcout << L" -- var a =" << var(a_in) << L"--\n";
	  //wcout << L" -- var b =" << var(b_in) << L"--\n";

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
	      if (a.l == F & b.l == F)
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

	        		bdd_or ( bdd_or(bitwiseAND(a.h,  b.l ), bitwiseAND(a.l,  b.h )) , bitwiseAND(a.l,  b.l )));
	    }
	  }

	  return c;

}

