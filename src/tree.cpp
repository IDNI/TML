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
#include "lp.h"
#ifdef DEBUG
#include "driver.h"
#endif
using namespace std;

bool ar_prefix(const ints& x, ints y) {
	if (!y[0]) y.erase(y.begin());
	if (y.size() < x.size()) return false;
	for (size_t n = 0; n < x.size(); ++n) if (x[n] != y[n]) return false;
	return true;
}

set<prefix> lp::tree_prefix(const prefix& p) const {
	set<prefix> r;
	auto lt = db.lower_bound({p.rel,{}}), ut = db.upper_bound({p.rel+1,{}});
	while (lt != ut) {
		if (lt->first.rel != p.rel) return r;
		if (ar_prefix(p.ar, lt->first.ar)) r.insert(lt->first);
		++lt;
	}
	return r;
}

void lp::get_tree(const prefix& p, size_t root, set<size_t>& done) {
	if (!done.emplace(root).second) return;
	const vector<ints> x = p.subarities();
	const vector<array<size_t, 2>> y = p.subterms();
	const size_t len = p.len();
	DBG(assert(x.size() == y.size());)
	for (size_t n = 0; n != x.size(); ++n)
		for (const prefix& z : tree_prefix({ p.rel, x[n] }))
			get_tree(z, bdd_or(trees_out.emplace(z,F).first->second,
					bdd_and(*db.at(z), bdd_subterm(root,
					y[n][0], y[n][1], len, z.len(),rng.bits)
					)), done);
}

void lp::get_tree(const prefix& p, size_t root) {
	set<size_t> done;
	get_tree(p, root, done);
}

void lp::get_trees() {
	for (auto x : trees)
		for (auto p : tree_prefix(x.first))
			get_tree(p, bdd_and(*db.at(p), bdd_expand(
				x.second, x.first.len(), p.len(), rng.bits)));
	auto it = db.end();
	for (auto x : trees) {
		if ((it = db.find(x.first)) == db.end())
			it = db.emplace(x.first, new size_t).first;
		*it->second = x.second;
	}
}
