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
#include <random>
#include <dlfcn.h>
#include "tables.h"

using namespace std;

extern uints perm_init(size_t n);

void tables::fact_builtin(const term& b) {
	blt_ctx c(b);
	bltins.run_head(c);
}

void tables::head_builtin(const bdd_handles& hs, const table& tbl, ntable tab) {
	blt_ctx c(term(false,tab,ints(tbl.len, 0), 0, tbl.idbltin));
	//COUT << "head_builtin: " << hs << endl;
	for (auto h : hs) decompress(h, tab, [&c, this] (const term& t){
		// ground builtin vars by decompressed head
		//COUT << "head_builtin t: " << t << endl;
		for (size_t n = 0; n != t.size(); ++n) c.g[n] = t[n];
		bltins.run_head(c);
	}, 0, true);
}

void tables::body_builtins(spbdd_handle x, alt* a, bdd_handles& hs) {
	if (x == hfalse) return; // return if grounding failed
	vector<blt_ctx> ctx;
	for (term bt : a->bltins) // create contexts for each builtin
		ctx.emplace_back(bt, a), ctx.back().hs = &hs;
	if (a->bltinvars.size())	{ // decompress grounded terms
	    decompress(x,0, [&ctx, this] (const term t) {
		for (blt_ctx& c : ctx) {
			c.g = c.t; // ground vars by decompressed term
			for (size_t n = 0; n != c.g.size(); ++n)
				if (c.g[n] < 0 && has(c.a->bltinvars, c.g[n]))
					c.g[n] = t[c.a->grnd->vm.at(c.g[n])];
			bltins.run_body(c);
		}
	    }, a->grnd->varslen);
	    // collect outputs
	    for (blt_ctx& c : ctx) for (auto out : c.outs) hs.push_back(out);
	} else for (blt_ctx& c : ctx) { // no grounding -> just run
		bltins.run_body(c);
		for (auto out : c.outs) hs.push_back(out); // collect outputs
	}
}

