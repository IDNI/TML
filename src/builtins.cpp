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
#include "tables.h"

using namespace std;

size_t blt_ctx::varpos(size_t arg) const { return a->vm.at(g[arg]); }

int_t blt_ctx::outvarpos(size_t oarg) const {
	size_t size = args == -1 ? g.size() : args;
	DBG(assert(oarg < oargs && oargs <= size);)
	int_t arg = size + oarg - oargs;
	return a->vm.at(t[arg]);
}

void blt_ctx::args_bodies(bdd_handles& hs, size_t len) {
	if (!a) return;
	if (len == 0) len = a->bltngvars.size();
	hs = bdd_handles(len, htrue);
	for (auto p : a->varbodies)
		if (has(a->bltngvars, p.first)) {
			for (size_t n = 0; n != len; ++n)
				if (arg(n) == p.first)
					hs[n] =	hs[n] && p.second->rlast;
		}
}

void builtins::run(blt_ctx& c, bool ishead) {
	blt_cache_key k;
	if (!ishead && !c.t.renew) {
		k = c.key();
		auto cit = cache.find(c.key());
		if (cit != cache.end()) {
			if (cit->second.first) c.outs = cit->second.second;
			return;
		}
	}
	auto it = find(c.t.idbltin);
	if (it == end()) return;
	if ((ishead && !it->second.has_head) ||
		(!ishead && !it->second.has_body)) o::err()
			<< "builtin head/body error" << std::endl;
	builtin& b = ishead ? it->second.head : it->second.body;
	c.args = b.args, c.nargs = b.nargs, c.oargs = b.oargs;
	#ifndef REMOVE_DICT_FROM_BUILTINS
	c.dict = dict;
	#endif // REMOVE_DICT_FROM_BUILTINS
	b.run(c);
	if (!ishead && !c.t.forget)
		cache.emplace(k, blt_cache_value(true, c.outs));
}
