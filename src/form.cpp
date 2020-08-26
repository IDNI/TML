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

#include "form.h"
#include "tables.h"

pnf_t::pnf_t(){
		varslen = 0, neg = false, b = NULL, cons = bdd_handle::T;
}

pnf_t::~pnf_t() {
		if(b) delete b, b = NULL;
		for (auto p: matrix ) delete p;
}
