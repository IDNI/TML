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
#ifndef __IDNI__TML__FORM_H__
#define __IDNI__TML__FORM_H__
#include <tuple>
#include <vector>
#include "defs.h"

namespace idni {

typedef std::shared_ptr<struct pnft> pnft_handle;
typedef const pnft_handle& cr_pnft_handle;

typedef enum {C, D} t_nf;

struct pnft {
	size_t varslen;
	size_t varslen_h;
	varmap vmh;
	bools ex_h;
	uints perm;
	uints perm_h;
	bool neg;
	std::vector<quant_t> quants;
	std::vector<quant_t> quantsh;
	std::vector<pnft_handle> matrix;

	body* b; //TODO make it vector for the disjunctive clause
	std::tuple<int_t, body*, int_t > hvar_b = {0,0,0}; //TODO make it vector?

	spbdd_handle cons;
	spbdd_handle last;
	std::set<body*, ptrcmp<body>> bodies;
	pnft();
	~pnft();
	quant_t to_quant_t(form *f) const;
	bool is_quant(form *f) const;
	bool fp(class tables *s) const;
	void print() const;
	void quantify(spbdd_handle &q, size_t bits) const;
};

struct var2space {
	varmap vm;
	t_nf nf = C;
	std::vector<int_t> hvars;
	std::map<int_t, bdd_handles> ins;
	std::map<int_t, bdd_handles> outs;
	std::vector<var2space> bf;
	var2space(varmap &vmh);
	~var2space();
	void add_cons(int id, spbdd_handle c);
	void add_cons_neg(int id, spbdd_handle c);
	void clear_cons();
	void negate_cons();
	void merge();
	void constraint(spbdd_handle q);
	void print(int_t level = 0) const;
	bool quantify(std::vector<quant_t> &quantsh) const;
};

} // idni namespace
#endif // __IDNI__TML__FORM_H__
