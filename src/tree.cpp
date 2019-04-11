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

bool tree_prefix(const ints& x, ints y) {
	if (!y[0]) y.erase(y.begin());
	if (y.size() < x.size()) return false;
	for (size_t n = 0; n < x.size(); ++n) if (x[n] != y[n]) return false;
	return true;
}

set<prefix> tree_prefix(const db_t& db, const prefix& p) {
	set<prefix> r;
	auto lt = db.lower_bound({p.rel,{}}), ut = db.upper_bound({p.rel+1,{}});
	while (lt != ut) {
		if (lt->first.rel != p.rel) return r;
		if (tree_prefix(p.ar, lt->first.ar)) r.insert(lt->first);
		++lt;
	}
	return r;
}

void get_tree(const prefix& p, size_t root, const db_t& db, size_t bits,
	diff_t& res, set<size_t>& done) {
	if (!done.emplace(root).second) return;
	//DBG(drv->printdb(wcout << "db:" << endl, db, bits));
	//DBG(drv->printdiff(wcout << "res:" << endl, res, bits));
	const vector<ints> x = p.subarities();
	const vector<array<size_t, 2>> y = p.subterms();
	const size_t len = p.len();
	DBG(assert(x.size() == y.size());)
	auto it = res.end();
	for (size_t n = 0, r; n != x.size(); ++n)
		for (const prefix& z : tree_prefix(db, { p.rel, x[n]})) {
			r = bdd_subterm(root,y[n][0],y[n][1],len,z.len(),bits);
			//DBG(drv->printbdd(wcout<<"subterm:"<<endl,r,bits,z,rel);)
			it = res.emplace(z, F).first;
			it->second = bdd_or(it->second, bdd_and(*db.at(z),r));
			get_tree(it->first, it->second, db, bits, res, done);
		}
}

void get_tree(const prefix& p, size_t root, const db_t& db, size_t bits,
	diff_t& res) {
	set<size_t> done;
	get_tree(p, root, db, bits, res, done);
}

void lp::get_trees() {
	auto it = db.end();
	for (auto x : trees)
		for (auto p : tree_prefix(db, x.first))
			if ((it = db.find(x.first)) != db.end())
				get_tree(it->first, bdd_and(*it->second,
					bdd_expand(x.second,
					x.first.len(), it->first.len(),
					rng.bits)),
					db, rng.bits, trees_out);
	for (auto x : trees) *db[x.first] = x.second;
}
