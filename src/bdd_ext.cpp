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
int_t bdd_root(cr_spbdd_handle x) {
	return (bdd::var(x->b));
}

void bdd_size(cr_spbdd_handle x,  std::set<int_t>& s) {
	bdd::bdd_sz_abs(x->b, s);
}

//------------------------------------------------------------------------------
spbdd_handle bdd_quantify(cr_spbdd_handle x, const std::vector<quant_t> &quants,
		const size_t bits, const size_t n_args) {
	return bdd_handle::get(bdd::bdd_quantify(x->b, 0, quants, bits, n_args));
}

spbdd_handle bdd_not(cr_spbdd_handle x) {
	return bdd_handle::get(-x->b);
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

spbdd_handle bdd_adder(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::adder(x->b,y->b, false, 0));
}

spbdd_handle bdd_mult_dfs(cr_spbdd_handle x, cr_spbdd_handle y, size_t bits,
		size_t n_vars ) {
	//bdds
	int_t *z_aux = new int_t[bits];
	int_t c = F;
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
int_t bdd::bdd_quantify(int_t x, int_t bit, const std::vector<quant_t> &quants,
		const size_t bits, const size_t n_args) {
	//if (x == T || x == F || bit == (int_t) quants.size() * (int_t) bits) return x;
	if (bit == (int_t) quants.size() * (int_t) bits) return x;
	size_t idx = bit/bits;
	if (x == T || x == F) {
		if (quants[idx] == quant_t::UN) return F;
		return x;
	}
	bdd c = get(x);
	int_t h,l;
	if (c.v > (int_t) quants.size() * (int_t) bits) return x;
	if (c.v > bit+1) {//TODO review for UNIQUE
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
			if (l == F || h == F) return add(c.v, h, l);
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

void bdd::bdd_sz_abs(int_t x, set<int_t>& s) {
	if (!s.emplace(abs(x)).second) return;
	bdd b = get(x);
	bdd_sz_abs(b.h, s), bdd_sz_abs(b.l, s);
}

int_t bdd::bitwise_and(int_t a_in, int_t b_in) {
	bdd a = get(a_in), b = get(b_in);
	if (a_in == T && b_in == T) return T;
	else if (a_in == F || b_in == F) return F;
	uint_t pos = 0;
	if (a.v > b.v + 1 && b.v != 0) {
		a.h = a_in, a.l = a_in;
	  	pos = b.v+1;
	} else if (a.v + 2 < b.v && a.v != 0) {
		b.h = b_in, b.l = b_in;
		pos = a.v + 2;
	} else if (a.v != 0) pos = a.v+2;
	else pos = b.v + 1;
	int_t c = add(pos, bitwise_and(a.h, b.h), bdd_or(bdd_or(bitwise_and(a.h,  b.l),
						bitwise_and(a.l, b.h)), bitwise_and(a.l,  b.l))
					);
	return c;
}

int_t bdd::bitwise_or(int_t a_in, int_t b_in) {
	bdd a = get(a_in), b = get(b_in);
	if (a_in == T && b_in == T) return T;
	else if (a_in == F || b_in == F) return F;
	uint_t pos = 0;
	if (a.v > b.v + 1 && b.v != 0) {
		a.h = a_in, a.l = a_in;
		pos = b.v+1;
	} else if (a.v + 2 < b.v && a.v != 0) {
		b.h = b_in, b.l = b_in;
		pos = a.v + 2;
	} else if (a.v != 0) pos = a.v+2;
	else pos = b.v + 1;
	int_t c = add(pos, bdd_or( bdd_or(bitwise_or(a.h, b.l), bitwise_or(a.l, b.h)),
						bitwise_or(a.h, b.h)), bitwise_or(a.l, b.l)
					);
	return c;
}

int_t bdd::bitwise_xor(int_t a_in, int_t b_in) {
	bdd a = get(a_in), b = get(b_in);
	if (a_in == T && b_in == T) return T;
	else if (a_in == F || b_in == F) return F;
	uint_t pos = 0;
	if (a.v > b.v + 1 && b.v != 0) {
		a.h = a_in, a.l = a_in;
		pos = b.v + 1;
	} else if (a.v + 2 < b.v && a.v != 0) {
		b.h = b_in, b.l = b_in;
		pos = a.v + 2;
	} else if (a.v != 0) pos = a.v + 2;
	else pos = b.v + 1;
	int_t c = add(pos, bdd_or(bitwise_xor(a.h, b.l), bitwise_xor(a.l, b.h)),
				  	bdd_or(bitwise_xor(a.h, b.h), bitwise_xor(a.l, b.l))
					);
	return c;
}

int_t bdd::bitwise_not(int_t a_in) {
	//TODO: implement
	return a_in;
}

int_t bdd::adder(int_t a_in, int_t b_in, bool carry, size_t bit) {

	bdd a = get(a_in), b = get(b_in);
	int_t c = 0;
	if (a_in == T && b_in == T)
		c = T;
	else if (a_in == F || b_in == F)
		c = F;
	else {
		int_t pos = 0;
		if (a.v > b.v + 1 && b.v != 0) {
			a.h = a_in, a.l = a_in;
		  	pos = b.v + 1;
		} else if (a.v + 2 < b.v && a.v != 0) {
			b.h = b_in, b.l = b_in;
			pos = a.v + 2;
		} else if (a.v != 0)
			pos = a.v + 2;
		else
			pos = b.v + 1;

		if (carry == false)
			c = add(pos,
					bdd_or(adder(a.h, b.l, false, bit+1), adder(a.l, b.h, false, bit+1)),
					bdd_or(adder(a.h, b.h, true,  bit+1), adder(a.l, b.l, false, bit+1)));
		else
			c = add(pos,
					bdd_or(adder(a.h, b.h, true, bit+1), adder(a.l, b.l, false, bit+1)),
					bdd_or(adder(a.h, b.l, true, bit+1), adder(a.l, b.h, true,  bit+1)));
	}
	return c;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// Over bdds MULT
// ----------------------------------------------------------------------------

extern uints perm_init(size_t n);

template<typename T> struct veccmp {
	bool operator()(const vector<T>& x, const vector<T>& y) const{
		if (x.size() != y.size()) return x.size() < y.size();
		return x < y;
	}
};
extern map<uints, unordered_map<int_t, int_t>, veccmp<uint_t>> memos_perm;
// ----------------------------------------------------------------------------
std::map<size_t, int_t> covered_cf;
std::map<size_t, int_t> covered_ct;

int_t bdd::merge_pathX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	int_t c;

	if (!carry) {
		std::map<size_t,int_t>::iterator it = covered_cf.find(i);
		if (it != covered_cf.end() && pathX_a.size() == 0 && pathX_b.size() == 0 ) {
			c = covered_cf[i];
		} else {
			c = solve_path(i,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			covered_cf[i] = c;
		}
	} else {
		std::map<size_t,int_t>::iterator it = covered_ct.find(i);
		if (it != covered_ct.end() && pathX_a.size() == 0 && pathX_b.size() == 0 ) {
			c = covered_ct[i];
		} else {
			c = solve_path(i,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			covered_ct[i] = c;
		}
	}
	return c;
}

int_t bdd::solve_pathXL(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	int_t pos = i * n_args + 3;
	int_t c = T;

	if (path_a[bits-i-1] == X && path_b[bits-i-1] == L) {

		if (pathX_b.size() == 0) {

			t_pathv aux_pathX_a = pathX_a;
			#ifdef VERBOSE
			COUT << " ---solve XL pos = " << pos << "\n";
			#endif
			pathX_a.push_back(L);
			int_t c0;
			c0 = solve_pathXL(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);

			pathX_a = aux_pathX_a;
			#ifdef VERBOSE
			COUT << " ---solve XL pos = " << pos << "\n";
			#endif
			pathX_a.push_back(H);
			int_t c1;
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
			int_t c0;
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

int_t bdd::solve_pathLX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	int_t pos = i * n_args + 3;
	int_t c = T;

	if (path_a[bits-i-1] == L && path_b[bits-i-1] == X) {
		if (pathX_a.size() == 0) {


			t_pathv aux_pathX_b = pathX_b;
			#ifdef VERBOSE
			COUT << " ---solve LX pos = " << pos << "\n";
			#endif
			pathX_b.push_back(L);
			int_t c0;
			c0 = solve_pathLX(i+1,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);

			pathX_b = aux_pathX_b;
			#ifdef VERBOSE
			COUT << " ---solve LX pos = " << pos << "\n";
			#endif
			pathX_b.push_back(H);
			int_t c1;
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
			int_t c0;
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

int_t bdd::solve_pathXH(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	int_t pos = i * n_args + 3;
	int_t c = T;

	if (path_a[bits-i-1] == X && path_b[bits-i-1] == H) {

		if (pathX_b.size() == 0) {

			t_pathv aux_pathX_a = pathX_a;
			#ifdef VERBOSE
			COUT << " ---solve XH pos = " << pos << "\n";
			#endif
			pathX_a.push_back(L);
			int_t c0, c1;
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
			int_t c0;
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

int_t bdd::solve_pathHX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {
	int_t pos = i * n_args + 3;
	int_t c = T;

	if (path_a[bits-i-1] == H && path_b[bits-i-1] == X) {

		if (pathX_a.size() == 0) {

			t_pathv aux_pathX_b = pathX_b;
			#ifdef VERBOSE
			COUT << " ---solve HX pos = " << pos << "\n";
			#endif
			pathX_b.push_back(L);
			int_t c0, c1;
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
			int_t c0;
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

int_t bdd::solve_pathXX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	int_t c = T;
	int_t pos = i * n_args + 3;


	if (path_a[bits-i-1] == X && path_b[bits-i-1] == X) {

		if (pathX_a.size() == 0 && pathX_b.size() == 0) {
			while (path_a[bits-i-1] == X && path_b[bits-i-1] == X) i++;
			//t_pathv aux_pathX_a = pathX_a;
			//t_pathv aux_pathX_b = pathX_b;
			int_t c0 = solve_path(i,bits, false, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			//int_t c1 = solve_path(i,bits, true, n_args, depth, path_a, path_b, aux_pathX_a, aux_pathX_b);
			int_t c1 = solve_path(i,bits, true, n_args, depth, path_a, path_b, pathX_a, pathX_b);
			c = add(pos, bdd_or(c0,c1), F);
		}
		else {
			#ifdef VERBOSE
			COUT << " ---solve XX pos = " << pos << "\n";
			#endif
			t_path aux;
			int_t c0,c1,ch = F, cl = F;

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

int_t bdd::solve_path(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
		t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b) {

	if (i == bits)
		return T;

	int_t c = T;
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

void bdd::satcount_arith(bdd a, size_t bit, size_t bits, size_t factor, size_t n_args,
		size_t &count) {

	if (a.h == F && a.l == F) return;
	if (a.h == T && a.l == T) {
		count = count + factor * pow(2, bits-bit); return;
	}
	if (a.h != F) {
		bdd ah = get(a.h);
		size_t delta = a.h != T ? (ah.v - a.v)/n_args : 1;
		satcount_arith(ah, bit+delta, bits, factor * delta, n_args,count);
	}
	if (a.l != F) {
		bdd al = get(a.l);
		size_t delta = a.l != T ? (al.v - a.v)/n_args : 1;
		satcount_arith(al, bit+delta, bits, factor * delta,  n_args,count);
	}
	return;
}

bool bdd::bdd_next_path(std::vector<bdd> &a, int_t &i, int_t &bit, t_pathv &path,
		size_t bits, size_t n_args) {

	//size_t bit, size_t bits, size_t factor,
	bool done = false;
	bool goh = false;

	while (!done) {
		if (path[bit] == U)
			done = true;
		else if (path[bit] == L && a[i].h != F) {
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

	if (a[i].h == F && a[i].l == F) {
		return false;
	}

	done = false;
	while (!done) {
		if (a[i].l != F && !goh) {
			if (a[i].l == T) {
				done = true;
				size_t delta =  bits-bit;
				path[bit] = L;
				if (delta > 1)
					for(size_t j = 1; j < delta; j++) path[bit+j] = X;
			}
			else {
				a.push_back(get(a[i].l)); //a[i].l;

				size_t delta = (a[i+1].v - a[i].v)/n_args;
				path[bit] = L;
				if (delta > 1)
					for(size_t j = 1; j < delta; j++) path[bit+j] = X;
				i++;
				bit = bit+delta;
			}
		}
		else if (a[i].h != F) {
			goh = false;
			if (a[i].h == T) {
				done = true;
				size_t delta =  bits-bit;
				path[bit] = H;
				if (delta > 1)
					for(size_t j = 1; j < delta; j++) path[bit+j] = X;
			}
			else {
				a.push_back(get(a[i].h)); //a[i].l;
				size_t delta = (a[i+1].v - a[i].v)/n_args;
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

void bdd::adder_be(int_t a_in, int_t b_in, size_t bits, size_t depth,
		size_t n_args, int_t &c) {

	t_pathv path_a(bits, U);
	t_pathv path_b(bits, U);

	t_pathv next_path_a;
	t_pathv next_path_b;

	t_pathv pathX_a;
	t_pathv pathX_b;

	std::vector<t_pathv> aux_path_a;
	std::vector<t_pathv> aux_path_b;

	std::vector<bdd> a;
	std::vector<bdd> b;
	a.push_back(get(a_in));
	b.push_back(get(b_in));

	int_t a_i = 0;
	int_t a_bit = 0;
	int_t b_i = 0;
	int_t b_bit = 0;

	bool a_path_vld = true;
	bool b_path_vld = true;

	int_t aux;

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

int_t bdd::shlx(int_t b_in, size_t x, size_t bits, size_t n_args) {

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
	int_t aux = bdd_permute(b_in, perm1, memos_perm[perm1]);
	int_t aux_b = aux;
	for (size_t i = 0; i < x ; i++) {
		aux_b = add((n_args*(x-i-1))+2,F,aux_b);
	}
	return aux_b;
}

int_t bdd::shr(int_t a_in, size_t arg, size_t bits, size_t n_args) {

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
	int_t aux_bit = add(pos_z,F,T);
	a_in = bdd_and(a_in, aux_bit);
	return a_in;
}

int_t bdd::copy(int_t a_in) {
	 if (a_in == T) return T;
	 else if (a_in == F) return F;
	 bdd a = get(a_in);
	 int_t pos = a.v + 1;
 	 int_t c = add(pos, copy(a.h) , copy(a.l));
 	 return c;
}

int_t bdd::copy_arg2arg(int_t a , size_t arg_a, size_t arg_b, size_t bits,
	size_t n_args) {
	int_t b;
	uints perm = perm_init(bits*n_args);
	for (size_t i = 0; i < bits; i++) {
		//COUT << perm[i*n_args + arg_a]+1 << " --- " << i*n_args + arg_b +1 << "\n";
		perm[i*n_args + arg_a] = i*n_args + arg_b;
	}
	b = bdd_permute(a, perm, memos_perm[perm]);
	return b;
}

int_t bdd::adder_accs(int_t b_in, int_t acc, size_t depth, size_t bits,
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
	int_t aux_ext = T;
	for (size_t i = bits; i < ext_bits ; i++) {
		pos_z = n_args * i + 2; //to update arg b (#2)
		aux_ext = bdd_and(aux_ext, add(pos_z, F, T));
	}

	int_t b_aux = shlx(b_in, depth, bits, n_args);
	//COUT << "##[baux]:" << endl;
	//out(COUT, b_aux);
	//COUT <<endl<<endl;
	aux_ext = T;
	for (size_t i = bits; i < ext_bits ; i++) {
		pos_z = n_args * i + 3;
		aux_ext = bdd_and(aux_ext, add(pos_z, F, T));
	}
	int_t acc_aux = bdd_and(acc,aux_ext);
	//COUT << "##[acc_aux]:" << endl;
	//out(COUT, acc_aux);
	//COUT <<endl<<endl;
	int_t aux = F;
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

int_t bdd::zero(size_t arg, size_t bits, size_t n_args) {

	int_t aux = T;
	int_t pos;
	for (size_t i = 0; i < bits; i++) {
		pos = n_args * (bits-1-i) + arg;
		aux = add(pos, F, aux);
	}
	return aux;
}

bool bdd::is_zero(int_t a_in, size_t bits) {
	bdd a = get(a_in);
	for (size_t i = 0; i < bits; i++) {
		if (a.h != F) return false;
		a = get(a.l);
	}
	return true;
}

void bdd::mult_dfs(int_t a_in, int_t b_in, int_t *accs, size_t depth, size_t bits,
	size_t n_args, int_t &c) {

	if (depth == bits) {
		c = bdd_or(c, accs[depth-1]);
		return ;
	}
	int_t pos = n_args * depth + 1;
	bdd a = get(a_in);
	if (a.v > pos) {a.h = a_in, a.l = a_in;}
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
