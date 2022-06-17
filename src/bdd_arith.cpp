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
#include "math.h"
using namespace std;

//------------------------------------------------------------------------------
// auxiliary functions
bdd_shft bdd_root(cr_spbdd_handle x) {
	return (bdd::var(x->b));
}

void bdd_size(cr_spbdd_handle x, std::set<bdd_id>& s) {
	bdd::bdd_sz_abs(x->b, s);
}

//------------------------------------------------------------------------------
spbdd_handle bdd_quantify(cr_spbdd_handle x, const std::vector<quant_t> &quants,
		const size_t bits, const size_t n_args) {
	return bdd_handle::get(bdd::bdd_quantify(x->b, 0, quants, bits, n_args));
}

spbdd_handle bdd_not(cr_spbdd_handle x) {
	return bdd_handle::get(FLIP_INV_OUT(x->b));
}

size_t satcount(cr_spbdd_handle x, const size_t bits) {
	bdd_shft av = GET_SHIFT(x->b);
	size_t cnt = 0;
	size_t factor = x->b != T ? pow(2,av-1) : 1;
	size_t bit = (x->b != T && x->b != F) ? (av)-1 : 0;
	bdd::satcount_arith(x->b, bit, bits, factor, cnt);
	return cnt;
}

//------------------------------------------------------------------------------
//over bdd bitwise operators
spbdd_handle bdd_bitwise_and(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bitwise_and(x->b,y->b));
}

spbdd_handle bdd_bitwise_or(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bitwise_or(x->b,y->b));
}

spbdd_handle bdd_bitwise_xor(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bitwise_xor(x->b,y->b));
}

spbdd_handle bdd_bitwise_not(cr_spbdd_handle x) {
	return bdd_handle::get(bdd::bitwise_not(x->b));
}

// over bdd arithmetic
spbdd_handle bdd_leq(cr_spbdd_handle x, cr_spbdd_handle y,
		const size_t x_bitw, const size_t y_bitw/*, size_t x_idx, size_t y_idx*/) {
	return bdd_handle::get(bdd::leq(x->b,y->b, 0, x_bitw, y_bitw/*, x_idx, y_idx*/));
}

spbdd_handle bdd_adder(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::adder(x->b,y->b, false, 0));
}

spbdd_handle bdd_mult_dfs(cr_spbdd_handle x, cr_spbdd_handle y, size_t bits,
		size_t n_vars ) {
	//bdds
	bdd_ref *z_aux = new bdd_ref[bits];
	bdd_ref c = F;
	bdd::mult_dfs(x->b, y->b, z_aux, 0, bits, n_vars, c);
	delete[] z_aux;
	size_t ext_bits = 2*bits;
	bools exvec;
	for (size_t i = 0; i < ext_bits*n_vars; ++i) {
		if (i > n_vars*bits)
			exvec.push_back(true);
		else exvec.push_back(false);
	}
	c = bdd::bdd_ex(c, exvec);
	return bdd_handle::get(c);
}

// ----------------------------------------------------------------------------
bdd_ref bdd::bdd_quantify(bdd_ref x, uint_t bit, const std::vector<quant_t> &quants,
		const size_t bits, const size_t n_args) {
	//if (x == T || x == F || bit == (int_t) quants.size() * (int_t) bits) return x;
	if (bit == quants.size() * bits) return x;
	size_t idx = bit/bits;
	if (x == T || x == F) {
		if (quants[idx] == quant_t::UN) return F;
		return x;
	}
	bdd c = bdd::get(x);
	bdd_ref h,l;
	if (GET_SHIFT(x) > quants.size() * bits) return x;
	if (GET_SHIFT(x) > bit+1) {//TODO review for UNIQUE
		if (quants[idx] == quant_t::UN) return F;
		return bdd_quantify(x, bit+1, quants, bits, n_args);
	}

	switch (quants[idx]) {
		case quant_t::FA: {
			if (c.l == F || c.h == F) return F;
			h = bdd_quantify(c.h, bit+1, quants, bits, n_args);
			if (h == F) return F;
			l =	bdd_quantify(c.l, bit+1, quants, bits, n_args);
			if (l == F) return F;
			return x;
		}
		case quant_t::EX: {
			h = bdd_quantify(c.h, bit+1, quants, bits, n_args);
			l =	bdd_quantify(c.l, bit+1, quants, bits, n_args);
			if (l == F && h == F) return F;
			if (l == F || h == F) return add(GET_SHIFT(x), h, l);
			return x;
		}
		case quant_t::UN: {
			if (c.l != F && c.h != F) return F;
			h = bdd_quantify(c.h, bit+1, quants, bits, n_args);
			l =	bdd_quantify(c.l, bit+1, quants, bits, n_args);
			if ((l == F && h == F) || (l == T && h == T)) return F;
			return x;
		}
		default: ;
	}
	return F;
}

void bdd::satcount_arith(bdd_ref a, size_t bit, size_t bits, size_t factor,
		size_t &count) {
	bdd ab = bdd::get(a);
	bdd_shft av = GET_SHIFT(a);
	if (ab.h == F && ab.l == F) return;
	if (ab.h == T && ab.l == T) {
		count = count + factor * pow(2, bits-bit); return;
	}
	if (ab.h != F) {
		size_t delta = ab.h != T ? pow(2, GET_SHIFT(ab.h) - av - 1) : 1;
		satcount_arith(ab.h, av, bits, factor * delta, count);
	}
	if (ab.l != F) {
		size_t delta = ab.l != T ? pow(2, GET_SHIFT(ab.l) - av - 1) : 1;
		satcount_arith(ab.l, av, bits, factor * delta, count);
	}
	return;
}

/*
void bdd::satcount_arith_ex(bdd a, size_t bit, const size_t bits, size_t factor,
		const bools &ex, size_t &count) {
	//work in progress
	if (a.h == F && a.l == F) return;
	if (a.h == T && a.l == T) {
		count = count + factor * pow(2, bits-bit); return;
	}
	if (a.h != F) {
		bdd ah = get(a.h);
		size_t delta = a.h != T ? pow(2,(ah.v - a.v)-1) : 1;
		satcount_arith_ex(ah, a.v, bits, factor * delta, ex, count);
	}
	if (a.l != F) {
		bdd al = get(a.l);
		size_t delta = a.l != T ? pow(2,(al.v - a.v)-1) : 1;
		satcount_arith_ex(al, a.v, bits, factor * delta, ex, count);
	}
	return;
}
*/

// ----------------------------------------------------------------------------
/*
int_t bdd::max(int_t a_in, size_t bit, size_t x_bitw) {
	if (a_in == F)
		return F;
	if (a_in == T) {
	}
}*/

/*
//...
if (a.v > b.v + 1 && b.v != 0) {
		a.h = a_in, a.l = a_in;
	  	pos = b.v + 1;
	} else if (a.v + 2 < b.v && a.v != 0) {
		b.h = b_in, b.l = b_in;
		pos = a.v + 2;
	} else {
		pos = a.v + 2;
}
*/

bdd_ref bdd::leq(bdd_ref a_in, bdd_ref b_in, size_t bit, const size_t x_bitw,
		const size_t y_bitw /*, size_t x_idx = 0, size_t y_idx = 0*/) {

	bdd_ref c = T;
	//COUT << " ... bdd leq handler ...  " << "\n";
	bdd a = get(a_in);
	bdd b = get(b_in);
	//COUT << "arg0: root(" << a.v << ") " << x_idx <<":"<<x_bitw << endl;
	//COUT << "arg1: root(" << b.v << ") " << y_idx <<":"<<y_bitw << endl;
	//COUT << endl; out(COUT, a_in);
	//COUT << endl; out(COUT, b_in);
	//COUT << endl;

	size_t pos = 0;
	size_t delta = 1;

	if (a_in == F || b_in == F) return F;
	if (b_in == T) return a_in;
	if ( (a_in == T) ||
	     (GET_SHIFT(a_in) + (int_t)x_bitw > GET_SHIFT(b_in)) ) {
		//pos = b.v + 2; ... on interleaved
		pos = GET_SHIFT(b_in) - x_bitw + (y_bitw - x_bitw);
		if (b.h != F) c = add(pos, leq(a_in, b.h, pos, x_bitw, y_bitw/*, x_idx, y_idx*/), T);
		else c = add(pos, F, leq(a_in,b.l, pos, x_bitw, y_bitw/*, x_idx, y_idx*/));
	}
	else {
		if (GET_SHIFT(a_in) + (int_t )x_bitw == GET_SHIFT(b_in)) pos = GET_SHIFT(a_in) + (y_bitw - x_bitw);
		else pos = GET_SHIFT(a_in);

		if (b.h != F)
			c = add(pos, leq(a.h, b.h, pos, x_bitw, y_bitw/*, x_idx, y_idx*/), a.l);
		else {
			if (pos-1 > bit) {
				c = add(pos, leq(a.h,b.l, bit+delta, x_bitw, y_bitw/*, x_idx, y_idx*/), a.l );
				c = add(pos-1, F, c );
			}
			else c = add(pos, F, leq(a.l, b.l, pos, x_bitw, y_bitw/*, x_idx, y_idx*/));
		}
	}
	return c;
}

/*
int_t bdd::geq(int_t a_in, int_t b_in, size_t bit, size_t x_bitw, size_t y_bitw) {

	int_t c = T;
	//COUT << " ... bdd geq handler ...  " << "\n";
	bdd a = get(a_in);
	bdd b = get(b_in);
	int_t pos = 0;
	int_t delta = 1;

	if (a_in == F || b_in == F) return F;
	if (b_in == T) return a_in;
	if ( (a_in == T) ||
	     (a.v + x_bitw > b.v) ) {
		//pos = b.v + 2; ... on interleaved
		pos = b.v - x_bitw + (y_bitw - x_bitw);
		if (b.h != F) c = add(pos, geq(a_in, b.h, pos, x_bitw, y_bitw), T);
		else c = add(pos, F, geq(a_in,b.l, pos, x_bitw, y_bitw));
	}
	else {
		if (a.v + x_bitw == b.v)pos = a.v + (y_bitw - x_bitw);
		else pos = a.v;

		if (b.h != F)
			c = add(pos, geq(a.h, b.h, pos, x_bitw, y_bitw), a.l);
		else {
			if (pos-1 > bit) {
				c = add(pos, geq(a.h,b.l, bit+delta, x_bitw, y_bitw), a.l );
				c = add(pos-1, F, c );
			}
			else c = add(pos, F, geq(a.l, b.l, pos, x_bitw, y_bitw));
		}
	}
	return c;
}
*/

void bdd::bdd_sz_abs(bdd_ref x, set<bdd_id>& s) {
	if (!s.emplace(GET_BDD_ID(x)).second) return;
	bdd b = get(x);
	bdd_sz_abs(b.h, s), bdd_sz_abs(b.l, s);
}

bdd_ref bdd::bitwise_and(bdd_ref a_in, bdd_ref b_in) {
	bdd a = bdd::get(a_in), b = bdd::get(b_in);
	if (a_in == T && b_in == T) return T;
	else if (a_in == F || b_in == F) return F;
	bdd_shft pos = 0;
	if (GET_SHIFT(a_in) > GET_SHIFT(b_in) + 1 && GET_SHIFT(b_in) != 0) {
		a.h = a_in, a.l = a_in;
	  	pos = GET_SHIFT(b_in)+1;
	} else if (GET_SHIFT(a_in) + 2 < GET_SHIFT(b_in) && GET_SHIFT(a_in) != 0) {
		b.h = b_in, b.l = b_in;
		pos = GET_SHIFT(a_in) + 2;
	} else if (GET_SHIFT(a_in) != 0) pos = GET_SHIFT(a_in)+2;
	else pos = GET_SHIFT(b_in) + 1;
	bdd_ref c = add(pos, bitwise_and(a.h, b.h), bdd_or(bdd_or(bitwise_and(a.h,  b.l),
						bitwise_and(a.l, b.h)), bitwise_and(a.l,  b.l))
					);
	return c;
}

bdd_ref bdd::bitwise_or(bdd_ref a_in, bdd_ref b_in) {
	bdd a = bdd::get(a_in), b = bdd::get(b_in);
	if (a_in == T && b_in == T) return T;
	else if (a_in == F || b_in == F) return F;
	bdd_shft pos = 0;
	if (GET_SHIFT(a_in) > GET_SHIFT(b_in) + 1 && GET_SHIFT(b_in) != 0) {
		a.h = a_in, a.l = a_in;
		pos = GET_SHIFT(b_in)+1;
	} else if (GET_SHIFT(a_in) + 2 < GET_SHIFT(b_in) && GET_SHIFT(a_in) != 0) {
		b.h = b_in, b.l = b_in;
		pos = GET_SHIFT(a_in) + 2;
	} else if (GET_SHIFT(a_in) != 0) pos = GET_SHIFT(a_in)+2;
	else pos = GET_SHIFT(b_in) + 1;
	bdd_ref c = add(pos, bdd_or( bdd_or(bitwise_or(a.h, b.l), bitwise_or(a.l, b.h)),
						bitwise_or(a.h, b.h)), bitwise_or(a.l, b.l)
					);
	return c;
}

bdd_ref bdd::bitwise_xor(bdd_ref a_in, bdd_ref b_in) {
	bdd a = bdd::get(a_in), b = bdd::get(b_in);
	if (a_in == T && b_in == T) return T;
	else if (a_in == F || b_in == F) return F;
	bdd_shft pos = 0;
	if (GET_SHIFT(a_in) > GET_SHIFT(b_in) + 1 && GET_SHIFT(b_in) != 0) {
		a.h = a_in, a.l = a_in;
		pos = GET_SHIFT(b_in) + 1;
	} else if (GET_SHIFT(a_in) + 2 < GET_SHIFT(b_in) && GET_SHIFT(a_in) != 0) {
		b.h = b_in, b.l = b_in;
		pos = GET_SHIFT(a_in) + 2;
	} else if (GET_SHIFT(a_in) != 0) pos = GET_SHIFT(a_in) + 2;
	else pos = GET_SHIFT(b_in) + 1;
	bdd_ref c = add(pos, bdd_or(bitwise_xor(a.h, b.l), bitwise_xor(a.l, b.h)),
				  	bdd_or(bitwise_xor(a.h, b.h), bitwise_xor(a.l, b.l))
					);
	return c;
}

bdd_ref bdd::bitwise_not(bdd_ref a_in) {
	//TODO: implement
	return a_in;
}

bdd_ref bdd::adder(bdd_ref a_in, bdd_ref b_in, bool carry, size_t bit) {
	bdd a = bdd::get(a_in), b = bdd::get(b_in);
	bdd_ref c = 0;

	if (a_in == T && b_in == T) return T;
	else if (a_in == F || b_in == F) return F;

	bdd_shft pos = 0, av = GET_SHIFT(a_in), bv = GET_SHIFT(b_in);
	if (av > bv + 1 && bv != 0) {
		a.h = a_in, a.l = a_in;
	  	pos = bv + 1;
	} else if (av + 2 < bv && av != 0) {
		b.h = b_in, b.l = b_in;
		pos = av + 2;
	} else {
		pos = av + 2;
	}

	if (pos > (bit+1) * 3) {
		size_t delta = (pos / 3)-1;
		if (carry)
			c = add(pos-3, bdd_or(adder(a_in, b_in,true,delta), adder(a_in, b_in,false,delta)), adder(a_in, b_in,true,delta));
		else
			c = add(pos-3,adder(a_in, b_in,false,delta) , bdd_or(adder(a_in, b_in,true,delta), adder(a_in, b_in,false,delta)));
		return c;
	}


	if (!carry)
		c = add(pos,
				bdd_or(adder(a.h, b.l, false, bit+1), adder(a.l, b.h, false, bit+1)),
				bdd_or(adder(a.h, b.h, true,  bit+1), adder(a.l, b.l, false, bit+1)));

	else
		c = add(pos,
				bdd_or(adder(a.h, b.h, true, bit+1), adder(a.l, b.l, false, bit+1)),
				bdd_or(adder(a.h, b.l, true, bit+1), adder(a.l, b.h, true,  bit+1)));
	return c;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// Over bdds MULT
// ----------------------------------------------------------------------------
#ifdef BDD_ARITH
extern uints perm_init(size_t n);
#else
uints perm_init(size_t n) {
	uints p(n);
	while (n--) p[n] = n;
	return p;
}
#endif

template<typename T> struct veccmp {
	bool operator()(const vector<T>& x, const vector<T>& y) const{
		if (x.size() != y.size()) return x.size() < y.size();
		return x < y;
	}
};
extern map<uints, unordered_map<bdd_ref, bdd_ref>, veccmp<uint_t>> memos_perm;
// ----------------------------------------------------------------------------
std::map<size_t, bdd_ref> covered_cf;
std::map<size_t, bdd_ref> covered_ct;

bdd_ref bdd::merge_pathX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	bdd_ref c;

	if (!carry) {
		std::map<size_t,bdd_ref>::iterator it = covered_cf.find(i);
		if (it != covered_cf.end() && pathX_a.size() == 0 && pathX_b.size() == 0 ) {
			c = covered_cf[i];
		} else {
			c = solve_path(i,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			covered_cf[i] = c;
		}
	} else {
		std::map<size_t,bdd_ref>::iterator it = covered_ct.find(i);
		if (it != covered_ct.end() && pathX_a.size() == 0 && pathX_b.size() == 0 ) {
			c = covered_ct[i];
		} else {
			c = solve_path(i,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			covered_ct[i] = c;
		}
	}
	return c;
}

bdd_ref bdd::solve_pathXL(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	int_t pos = i * n_args + 3;
	bdd_ref c = T;

	if (path_a[bits-i-1] == X && path_b[bits-i-1] == L) {

		if (pathX_b.size() == 0) {

			t_pathv aux_pathX_a = pathX_a;
			#ifdef VERBOSE
			COUT << " ---solve XL pos = " << pos << "\n";
			#endif
			pathX_a.push_back(L);
			bdd_ref c0;
			c0 = solve_pathXL(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);

			pathX_a = aux_pathX_a;
			#ifdef VERBOSE
			COUT << " ---solve XL pos = " << pos << "\n";
			#endif
			pathX_a.push_back(H);
			bdd_ref c1;
			if (!carry) {
				c1 = solve_pathXL(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				c = add(pos, c1, c0);
			} else {
				c1 = solve_pathXL(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				c = add(pos, c0, c1);
			}
		}
		else {

			t_path aux = pathX_b.front();
			pathX_b.erase(pathX_b.begin());
			#ifdef VERBOSE
			COUT << " ---solve XL pos = " << pos << "\n";
			#endif
			bdd_ref c0;
			if (!carry) {
				c0 = solve_pathXL(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				if (aux == L)
					c = add(pos, F, c0);
				else
					c = add(pos, c0, F);
			} else {
				if (aux == L) {
					c0 = solve_pathXL(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, c0, F);
				} else {
					c0 = solve_pathXL(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, F, c0);
				}
			}
		}
	}
	else {
		c = merge_pathX(i, bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		//c = solve_path(i,bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);
	}
	return c;
}

bdd_ref bdd::solve_pathLX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	int_t pos = i * n_args + 3;
	bdd_ref c = T;

	if (path_a[bits-i-1] == L && path_b[bits-i-1] == X) {
		if (pathX_a.size() == 0) {


			t_pathv aux_pathX_b = pathX_b;
			#ifdef VERBOSE
			COUT << " ---solve LX pos = " << pos << "\n";
			#endif
			pathX_b.push_back(L);
			bdd_ref c0;
			c0 = solve_pathLX(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);

			pathX_b = aux_pathX_b;
			#ifdef VERBOSE
			COUT << " ---solve LX pos = " << pos << "\n";
			#endif
			pathX_b.push_back(H);
			bdd_ref c1;
			if (!carry) {
				c1 = solve_pathLX(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				c = add(pos, c1, c0);
			} else {
				c1 = solve_pathLX(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				c = add(pos, c0, c1);
			}
		}
		else {
			t_path aux = pathX_a.front();
			pathX_a.erase(pathX_a.begin());
			#ifdef VERBOSE
			COUT << " ---solve LX pos = " << pos << "\n";
			#endif
			bdd_ref c0;
			if (!carry) {
				c0 = solve_pathLX(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				if (aux == L)
					c = add(pos, F, c0);
				else
					c = add(pos, c0, F);
			} else {
				if (aux == L) {
					c0 = solve_pathLX(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, c0, F);
				} else {
					c0 = solve_pathLX(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, F, c0);
				}
			}
		}

	}
	else {
		c = merge_pathX(i, bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		//c = solve_path(i,bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);
	}
	return c;
}

bdd_ref bdd::solve_pathXH(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	int_t pos = i * n_args + 3;
	bdd_ref c = T;

	if (path_a[bits-i-1] == X && path_b[bits-i-1] == H) {

		if (pathX_b.size() == 0) {

			t_pathv aux_pathX_a = pathX_a;
			#ifdef VERBOSE
			COUT << " ---solve XH pos = " << pos << "\n";
			#endif
			pathX_a.push_back(L);
			bdd_ref c0, c1;
			if (!carry)
				c0 = solve_pathXH(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			else
				c0 = solve_pathXH(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);

			pathX_a = aux_pathX_a;
			#ifdef VERBOSE
			COUT << " ---solve XH pos = " << pos << "\n";
			#endif
			pathX_a.push_back(H);

			if (!carry) {
				c1 = solve_pathXH(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				c = add(pos, c0, c1);
			} else {
				c1 = solve_pathXH(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				c = add(pos, c1, c0);
			}
		}
		else {

			t_path aux = pathX_b.front();
			pathX_b.erase(pathX_b.begin());
			#ifdef VERBOSE
			COUT << " ---solve XH pos = " << pos << "\n";
			#endif
			bdd_ref c0;
			if (!carry) {

				if (aux == L) {
					c0 = solve_pathXH(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, c0, F);
				} else {
					c0 = solve_pathXH(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, F, c0);
				}
			} else {
				if (aux == L) {
					c0 = solve_pathXH(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, F, c0);
				} else {
					c0 = solve_pathXH(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, c0, F);
				}
			}
		}
	}
	else {
		c = merge_pathX(i, bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		//c = solve_path(i,bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);
	}
	return c;
}

bdd_ref bdd::solve_pathHX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {
	int_t pos = i * n_args + 3;
	bdd_ref c = T;

	if (path_a[bits-i-1] == H && path_b[bits-i-1] == X) {

		if (pathX_a.size() == 0) {

			t_pathv aux_pathX_b = pathX_b;
			#ifdef VERBOSE
			COUT << " ---solve HX pos = " << pos << "\n";
			#endif
			pathX_b.push_back(L);
			bdd_ref c0, c1;
			if (!carry)
				c0 = solve_pathHX(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			else
				c0 = solve_pathHX(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);

			pathX_b = aux_pathX_b;
			#ifdef VERBOSE
			COUT << " ---solve HX pos = " << pos << "\n";
			#endif
			pathX_b.push_back(H);

			if (!carry) {
				c1 = solve_pathHX(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				c = add(pos, c0, c1);
			} else {
				c1 = solve_pathHX(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
				c = add(pos, c1, c0);
			}
		}
		else {

			t_path aux = pathX_a.front();
			pathX_a.erase(pathX_a.begin());
			#ifdef VERBOSE
			COUT << " ---solve HX pos = " << pos << "\n";
			#endif
			bdd_ref c0;
			if (!carry) {

				if (aux == L) {
					c0 = solve_pathHX(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, c0, F);
				} else {
					c0 = solve_pathHX(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, F, c0);
				}
			} else {
				if (aux == L) {
					c0 = solve_pathXH(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, F, c0);
				} else {
					c0 = solve_pathHX(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					c = add(pos, c0, F);
				}
			}
		}
	}
	else {
		c = merge_pathX(i, bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		//c = solve_path(i,bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);
	}
	return c;
}

bdd_ref bdd::solve_pathXX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	bdd_ref c = T;
	int_t pos = i * n_args + 3;


	if (path_a[bits-i-1] == X && path_b[bits-i-1] == X) {

		if (pathX_a.size() == 0 && pathX_b.size() == 0) {
			while (path_a[bits-i-1] == X && path_b[bits-i-1] == X) i++;
			//t_pathv aux_pathX_a = pathX_a;
			//t_pathv aux_pathX_b = pathX_b;
			bdd_ref c0 = solve_path(i,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			//int_t c1 = solve_path(i,bits, true, n_args, depth, path_a, path_b, aux_pathX_a, aux_pathX_b);
			bdd_ref c1 = solve_path(i,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			c = add(pos, bdd_or(c0,c1), F);
		}
		else {
			#ifdef VERBOSE
			COUT << " ---solve XX pos = " << pos << "\n";
			#endif
			t_path aux;
			bdd_ref c0,c1,ch = F, cl = F;

			t_pathv aux_pathX_a = pathX_a;
			t_pathv aux_pathX_b = pathX_b;

			if (pathX_a.size() > 0 ) {
				aux = pathX_a.front();
				pathX_a.push_back(L);
				pathX_a.erase(pathX_a.begin());
			} else {
				aux = pathX_b.front();
				pathX_b.push_back(L);
				pathX_b.erase(pathX_b.begin());
			}

			if (!carry) {
				if (aux == L) {
					c0 = solve_pathXX(i+1, bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					cl = add(pos, F, c0);
				} else {
					c1 = solve_pathXX(i+1, bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					cl = add(pos, c1, F);
				}
			} else {
				if (aux == L) {
					c1 = solve_pathXX(i+1, bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					cl = add(pos, c1, F);
				} else {
					c0 = solve_pathXX(i+1, bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					cl = add(pos, F, c0);
				}
			}

			 pathX_a = aux_pathX_a;
			 pathX_b = aux_pathX_b;

			if (pathX_a.size() > 0 ) {
				aux = pathX_a.front();
				pathX_a.push_back(H);
				pathX_a.erase(pathX_a.begin());
			} else {
				aux = pathX_b.front();
				pathX_b.push_back(H);
				pathX_b.erase(pathX_b.begin());
			}

			if (!carry) {
				if (aux == L) {
					c0 = solve_pathXX(i+1, bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					ch = add(pos, c0, F);
				} else {
					c0 = solve_pathXX(i+1, bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					ch = add(pos, F, c0);
				}
			} else {
				if (aux == L) {
					c0 = solve_pathXX(i+1, bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					ch = add(pos, F, c0);
				} else {
					c0 = solve_pathXX(i+1, bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
					ch = add(pos, c0, F);
				}
			}

			c = bdd_or(cl,ch);
		}

	} else {

		c = solve_path(i,bits, carry, n_args, depth, path_a, path_b, pathX_a, pathX_b);

	}

	return c;

}

bdd_ref bdd::solve_path(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	if (i == bits)
		return T;

	bdd_ref c = T;
	int_t pos = i * n_args + 3;
	#ifdef VERBOSE
	COUT << " ---solve pos = " << pos << "\n";
	#endif

	if (!carry) {
		if(path_a[bits-i-1] == L && path_b[bits-i-1] == L)
			c = add(pos, F, solve_path(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b));
		else if ((path_a[bits-i-1] == L && path_b[bits-i-1] == H) ||
				(path_a[bits-i-1] == H && path_b[bits-i-1] == L))
			c = add(pos, solve_path(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b), F);
		else if (path_a[bits-i-1] == H && path_b[bits-i-1] == H)
			c = add(pos, F, solve_path(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b));
		else if (path_a[bits-i-1] == X && path_b[bits-i-1] == H)
			c = solve_pathXH(i,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else if (path_a[bits-i-1] == H && path_b[bits-i-1] == X)
			c = solve_pathHX(i,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else if (path_a[bits-i-1] == X && path_b[bits-i-1] == L)
			c = solve_pathXL(i,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else if (path_a[bits-i-1] == L && path_b[bits-i-1] == X)
			c = solve_pathLX(i,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else if(path_a[bits-i-1] == X && path_b[bits-i-1] == X)
			c = solve_pathXX(i, bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else COUT << " --- ERROR" << "\n";
	}
	else  {
		if(path_a[bits-i-1] == L && path_b[bits-i-1] == L)
			c = add(pos, solve_path(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b), F);
		else if ((path_a[bits-i-1] == L && path_b[bits-i-1] == H) ||
				(path_a[bits-i-1] == H && path_b[bits-i-1] == L))
			c = add(pos, F, solve_path(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b));
		else if (path_a[bits-i-1] == H && path_b[bits-i-1] == H)
			c = add(pos, solve_path(i+1,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b), F);
		else if (path_a[bits-i-1] == X && path_b[bits-i-1] == H)
			c = solve_pathXH(i,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else if	(path_a[bits-i-1] == H && path_b[bits-i-1] == X)
			c = solve_pathHX(i,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else if (path_a[bits-i-1] == X && path_b[bits-i-1] == L)
			c = solve_pathXL(i,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else if (path_a[bits-i-1] == L && path_b[bits-i-1] == X)
			c = solve_pathLX(i,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else if(path_a[bits-i-1] == X && path_b[bits-i-1] == X)
			c = solve_pathXX(i, bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
		else COUT << " --- ERROR" << "\n";
	}

	//COUT << "##[C" << pos << "]:"<< endl;
	//out(COUT, c);
	//COUT <<endl<<endl;

	return c;
}

bool bdd::bdd_next_path(std::vector<bdd_ref> &a, int_t &i, int_t &bit, t_pathv &path,
		size_t bits, size_t n_args) {

	//size_t bit, size_t bits, size_t factor,
	bool done = false;
	bool goh = false;

	while (!done) {
		if (path[bit] == U)
			done = true;
		else if (path[bit] == L && bdd::hi(a[i]) != F) {
			done = true; goh = true;
		}
		else if (path[bit] != X) {
			path[bit] = U;
			bit--;
			a.pop_back();
			i--;
		} else {
			path[bit] = U;
			bit--;
		}
		if(bit < 0)
			return false;
	}

	if (bdd::hi(a[i]) == F && bdd::lo(a[i]) == F) {
		return false;
	}

	done = false;
	while (!done) {
		if (bdd::lo(a[i]) != F && !goh) {
			if (bdd::lo(a[i]) == T) {
				done = true;
				size_t delta =  bits-bit;
				path[bit] = L;
				if (delta > 1)
					for(size_t j = 1; j < delta; j++) path[bit+j] = X;
			}
			else {
				a.push_back(bdd::lo(a[i])); //bdd::lo(a[i]);

				size_t delta = (GET_SHIFT(a[i+1]) - GET_SHIFT(a[i]))/n_args;
				path[bit] = L;
				if (delta > 1)
					for(size_t j = 1; j < delta; j++) path[bit+j] = X;
				i++;
				bit = bit+delta;
			}
		}
		else if (bdd::hi(a[i]) != F) {
			goh = false;
			if (bdd::hi(a[i]) == T) {
				done = true;
				size_t delta =  bits-bit;
				path[bit] = H;
				if (delta > 1)
					for(size_t j = 1; j < delta; j++) path[bit+j] = X;
			}
			else {
				a.push_back(bdd::hi(a[i])); //bdd::lo(a[i]);
				size_t delta = (GET_SHIFT(a[i+1]) - GET_SHIFT(a[i]))/n_args;
				path[bit] = H;
				if (delta > 1)
					for(size_t j = 1; j < delta; j++) path[bit+j] = X;
				i++;
				bit = bit+delta;
			}
		}
	}
	return true;
}

int_t bdd::balance_paths(t_pathv &next_path_a, t_pathv &next_path_b, size_t bits,
		std::vector<t_pathv> &aux_path_a, std::vector<t_pathv> &aux_path_b) {

	size_t count_a = 1;
	size_t count_b = 1;

	assert(!(aux_path_a.size() != 0 && aux_path_b.size() != 0));

	if (aux_path_a.size() != 0) {
		next_path_a = aux_path_a.front();
		aux_path_a.erase(aux_path_a.begin());
	}
	if (aux_path_b.size() != 0) {
		next_path_b = aux_path_b.front();
		aux_path_b.erase(aux_path_b.begin());
	}

	for (size_t i = 0; i < bits ; i++ ) {
		if (next_path_a[i] == X) {
			count_a = count_a * 2;
		}
		if (next_path_b[i] == X) {
			count_b = count_b * 2;
		}
	}

	if (count_a == count_b) {
		if (aux_path_a.size() == 0 && aux_path_b.size() == 0) return 0;
		if (aux_path_a.size() != 0) return -1;
		if (aux_path_b.size() != 0) return 1;
		COUT << "ERROR" << endl;

	}

	if (count_a < count_b) {
		t_pathv aux_path(next_path_b);
		size_t i = 0;
		while (count_b > count_a) {
			if (next_path_b[i] == X) {
				next_path_b[i] = L;
				aux_path[i] = H;
				aux_path_b.insert(aux_path_b.begin(), aux_path);
				aux_path[i] = L;
				count_b = count_b >> 1;
			}
			i++;
		}
		return 1;
	}
	else {
		t_pathv aux_path(next_path_a);
		size_t i = 0;
		while (count_a > count_b) {
			if (next_path_a[i] == X) {
				next_path_a[i] = L;
				aux_path[i] = H;
				aux_path_a.insert(aux_path_a.begin(), aux_path);
				aux_path[i] = L;
				count_a = count_a >> 1;
			}
			i++;
		}
		return -1;
	}
}

void bdd::adder_be(bdd_ref a_in, bdd_ref b_in, size_t bits, size_t depth,
		size_t n_args, bdd_ref &c) {

	t_pathv path_a(bits, U);
	t_pathv path_b(bits, U);

	t_pathv next_path_a;
	t_pathv next_path_b;

	t_pathv pathX_a;
	t_pathv pathX_b;

	std::vector<t_pathv> aux_path_a;
	std::vector<t_pathv> aux_path_b;

	std::vector<bdd_ref> a;
	std::vector<bdd_ref> b;
	a.push_back(a_in);
	b.push_back(b_in);

	int_t a_i = 0;
	int_t a_bit = 0;
	int_t b_i = 0;
	int_t b_bit = 0;

	bool a_path_vld = true;
	bool b_path_vld = true;

	bdd_ref aux;

	a_path_vld = bdd_next_path(a, a_i, a_bit, path_a, bits, n_args);
	b_path_vld = bdd_next_path(b, b_i, b_bit, path_b, bits, n_args);

	next_path_a = path_a;
	next_path_b = path_b;
	while (a_path_vld && b_path_vld) {

		int_t bal = balance_paths(next_path_a, next_path_b, bits, aux_path_a, aux_path_b);

		if (a_path_vld && b_path_vld) {

			aux = solve_path(0, bits, false, n_args, depth, next_path_a, next_path_b, pathX_a, pathX_b);

			if (bal == 0) {
				a_path_vld = bdd_next_path(a, a_i, a_bit, path_a, bits, n_args);
				b_path_vld = bdd_next_path(b, b_i, b_bit, path_b, bits, n_args);
				next_path_a = path_a;
				next_path_b = path_b;

			}
			else if (bal == 1) {
				a_path_vld = bdd_next_path(a, a_i, a_bit, path_a, bits, n_args);
				next_path_a = path_a;
			}
			else {
				b_path_vld = bdd_next_path(b, b_i, b_bit, path_b, bits, n_args);
				next_path_b = path_b;
			}
			c = bdd_or(c, aux);
		}
	}
	covered_cf.clear();
	covered_ct.clear();
	return;
}

bdd_ref bdd::shlx(bdd_ref b_in, size_t x, size_t bits, size_t n_args) {

	uints perm1;
	size_t tbits = n_args*(bits+x);

	//FIXME: if perm1 is not assigned 0 to MSB that are getting "chopped"
	// we get wrong behavior from bdd_permute
	perm1 = perm_init(tbits);
	for (size_t i = 0; i < bits ; i++) {
		if (tbits-1 < n_args*(i+x)+1 ) {
			//COUT << perm1[n_args*i+1]+1 << " --- " << n_args*(i+x)+1+1 << "\n";
			perm1[n_args*i+1] = n_args*(i+x)+1 ;
		}
		else {
			//COUT << perm1[n_args*i+1]+1 << " --- " << perm1[n_args*(i+x)+1]+1 << "\n";
			perm1[n_args*i+1] = perm1[n_args*(i+x)+1];
		}
	}
	bdd_ref aux = bdd_permute(b_in, perm1, memos_perm[perm1]);
	bdd_ref aux_b = aux;
	for (size_t i = 0; i < x ; i++) {
		aux_b = add((n_args*(x-i-1))+2,F,aux_b);
	}
	return aux_b;
}

bdd_ref bdd::shr(bdd_ref a_in, size_t arg, size_t bits, size_t n_args) {

	size_t tbits = n_args*bits;
	size_t base = arg; // identifies which variable is being shifted
	bools exvec;
	for (size_t i = 0; i < tbits; ++i) {
		if (i == base)
			exvec.push_back(true);
		else exvec.push_back(false);
	}
	a_in = bdd_ex(a_in, exvec);

	uints perm1;
	for (size_t i = 1; n_args*i+base < tbits ; i++) {
		perm1[n_args*i+base] = perm1[n_args*i+base]-n_args;
	}
	a_in = bdd_permute(a_in, perm1, memos_perm[perm1]);
	size_t pos_z = n_args * (bits-1) + base + 1;
	bdd_ref aux_bit = add(pos_z,F,T);
	a_in = bdd_and(a_in, aux_bit);
	return a_in;
}

bdd_ref bdd::bdd_shift(bdd_ref a_in, bdd_shft amt) { return PLUS_SHIFT(a_in, amt); }

bdd_ref bdd::copy_arg2arg(bdd_ref a , size_t arg_a, size_t arg_b, size_t bits,
	size_t n_args) {
	bdd_ref b;
	uints perm = perm_init(bits*n_args);
	for (size_t i = 0; i < bits; i++) {
		//COUT << perm[i*n_args + arg_a]+1 << " --- " << i*n_args + arg_b +1 << "\n";
		perm[i*n_args + arg_a] = i*n_args + arg_b;
	}
	b = bdd_permute(a, perm, memos_perm[perm]);
	return b;
}

bdd_ref bdd::adder_accs(bdd_ref b_in, bdd_ref acc, size_t depth, size_t bits,
	size_t n_args) {

	size_t ext_bits = bits+depth;
	uints perm1;
	perm1 = perm_init(ext_bits*n_args);
	for (size_t i = 0; i < ext_bits*n_args; i++) {
		perm1[i] = ((ext_bits-1-(i/n_args))*n_args) + i % n_args;
	}

	size_t pos_z;
	//b extended
	//to concatenate leading '0's (MSB) to b
	//for depth = 0 (first acc), b ends bits + 2 (i.e bits = 3,  ext_bits = 5)
	bdd_ref aux_ext = T;
	for (size_t i = bits; i < ext_bits ; i++) {
		pos_z = n_args * i + 2; //to update arg b (#2)
		aux_ext = bdd_and(aux_ext, add(pos_z, F, T));
	}

	bdd_ref b_aux = shlx(b_in, depth, bits, n_args);
	//COUT << "##[baux]:" << endl;
	//out(COUT, b_aux);
	//COUT <<endl<<endl;
	aux_ext = T;
	for (size_t i = bits; i < ext_bits ; i++) {
		pos_z = n_args * i + 3;
		aux_ext = bdd_and(aux_ext, add(pos_z, F, T));
	}
	bdd_ref acc_aux = bdd_and(acc,aux_ext);
	//COUT << "##[acc_aux]:" << endl;
	//out(COUT, acc_aux);
	//COUT <<endl<<endl;
	bdd_ref aux = F;
	//XXX adder_be is returning aux LSB, no need to invert again
	if (is_zero(acc_aux, ext_bits))
		aux = copy_arg2arg(b_aux, 1,2,ext_bits, n_args);
	else {
		b_aux = bdd_permute(b_aux, perm1, memos_perm[perm1]);
		//COUT << "##[baux inv]:" << endl;
		//out(COUT, b_aux);
		//COUT <<endl<<endl;
		acc_aux = bdd_permute(acc_aux, perm1, memos_perm[perm1]);
		//COUT << "##[acc_aux inv]:" << endl;
		//out(COUT, acc_aux);
		//COUT <<endl<<endl;
		adder_be(b_aux, acc_aux, ext_bits, depth, n_args, aux);
	}
	//COUT << "##[adder_be]:" << endl;
	//out(COUT, aux);
	//COUT <<endl<<endl;
	return aux;
}

bdd_ref bdd::zero(size_t arg, size_t bits, size_t n_args) {

	bdd_ref aux = T;
	int_t pos;
	for (size_t i = 0; i < bits; i++) {
		pos = n_args * (bits-1-i) + arg;
		aux = add(pos, F, aux);
	}
	return aux;
}

bool bdd::is_zero(bdd_ref a_in, size_t bits) {
	bdd a = bdd::get(a_in);
	for (size_t i = 0; i < bits; i++) {
		if (a.h != F) return false;
		a = get(a.l);
	}
	return true;
}

void bdd::mult_dfs(bdd_ref a_in, bdd_ref b_in, bdd_ref *accs, size_t depth, size_t bits,
	size_t n_args, bdd_ref &c) {

	if (depth == bits) {
		c = bdd_or(c, accs[depth-1]);
		return ;
	}
	bdd_shft pos = n_args * depth + 1;
	bdd a = get(a_in);
	if (GET_SHIFT(a_in) > pos) {a.h = a_in, a.l = a_in;}
	if (a.l != F) {
		if (depth == 0)
			accs[depth] = zero(3, bits, n_args);
		else
			accs[depth] = accs[depth-1];
		mult_dfs(a.l, b_in, accs, depth+1, bits, n_args, c);
	}

	if (a.h != F) {
		//XXX improve to avoid call to is_zero once it has been false
		if (depth == 0)
			accs[depth] = copy_arg2arg(b_in, 1,2,bits, n_args);
		else
			accs[depth] = adder_accs(b_in, accs[depth-1], depth, bits, n_args);
		mult_dfs(a.h, b_in, accs, depth+1, bits, n_args, c);
	}
}

bdd_ref bdd::bdd_xor(bdd_ref x, bdd_ref y) { return bdd_ite(x,FLIP_INV_OUT(y),y); }

spbdd_handle bdd_xor(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_xor(x->b,y->b));
}

spbdd_handle bdd_shift(cr_spbdd_handle x, bdd_shft amt) {
	return bdd_handle::get(bdd::bdd_shift(x->b, amt));
}
