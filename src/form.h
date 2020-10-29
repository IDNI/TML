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

#ifndef _FORM_H_
#define _FORM_H_

#include <vector>
#include "defs.h"

template<typename T> struct ptrcmp_ {
	bool operator()(const T* x, const T* y) const { return *x < *y; }
};

typedef std::shared_ptr<struct pnft> pnft_handle;
typedef const pnft_handle& cr_pnft_handle;

struct pnft {
	size_t varslen;
	//TODO: replace vm by varslen_h
	varmap vm, vmh;
	bools ex;
	uints perm;
	uints perm_h;
	bool neg;
	std::vector<quant_t> quants;
	std::vector<quant_t> quantsh;
	std::vector<pnft_handle> matrix;

	body* b; //TODO make it vector for the disjunctive clause
	std::pair<int_t, body*> hvar_b = {0,0}; //vector

	spbdd_handle cons;
	spbdd_handle last;
	std::set<body*, ptrcmp_<body>> bodies;
	pnft();
	~pnft();
	quant_t to_quant_t(form *f) const;
	bool fp(class tables *s) const;
};
#endif
