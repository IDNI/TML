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

struct pnf_t {
	size_t varslen;
	varmap vm;
	bools ex;
	uints perm;
	uints perm_h;
	bool neg;

	std::vector<quant_t> quants;
	std::vector<pnf_t*> matrix;

	body* b;
	spbdd_handle cons;
	pnf_t();
	~pnf_t();
};

#endif /* SRCDIR_FORM_H_ */
