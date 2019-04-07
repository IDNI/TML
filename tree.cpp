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

vector<array<size_t, 2>> subterms(const ints& ar) {
	assert(ar.size() && ar[0] == 0);
	vector<array<size_t, 2>> r;
	for (size_t n = 1, from, last = 0, dep = 0; n != ar.size(); ++n) {
		if (ar[n] == -1) { if (!dep++) from = 0; }
		else if (ar[n] != -2) from += ar[n];
		else if (!--dep) r.push_back({last, last + from}), last = from;
	}
	return r;
}

vector<ints> subarities(const ints& ar) {
	vector<ints> r;
	ints x = {0};
	for (size_t n = ar[0] == 0 ? 1 : 0, dep = 0; n != ar.size(); ++n)
		if (x.push_back(ar[n]), ar[n] == -1) dep++;
		else if (ar[n] == -2 && !--dep) r.push_back(x), x = {0};
	return r;
}

bool prefix(ints x, ints y) {
	if (!x[0]) x.erase(x.begin());
	if (!y[0]) y.erase(y.begin());
	if (y.size() < x.size()) return false;
	for (size_t n = 0; n < x.size(); ++n) if (x[n] != y[n]) return false;
	return true;
}

set<ints> prefix(const db_t& db, ints ar, int_t rel) {
	set<ints> r;
	if (ar[0]) ar.insert(ar.begin(), 0);
	auto lt = db.lower_bound({rel,{}}), ut = db.upper_bound({rel+1,{}});
	while (lt != ut) {
		if (lt->first.first != rel) break;
		else if (prefix(ar, lt->first.second))
			r.insert(lt->first.second);
		++lt;
	}
	return r;
}

void get_tree(int_t rel, size_t root, ints ar, const db_t& db, size_t bits,
	diff_t& res, set<size_t>& done) {
	if (!done.emplace(root).second) return;
	DBG(drv->printdb(wcout << "db:" << endl, db, bits));
	DBG(drv->printdiff(wcout << "res:" << endl, res, bits));
	auto x = subarities(ar);
	auto y = subterms(ar);
	assert(x.size() == y.size());
	auto it = res.end();
	for (size_t n = 0, r; n != x.size(); ++n) {
		for (const ints& z : prefix(db, x[n], rel)) {
			r = bdd_subterm(root, y[n][0], y[n][1], arlen(ar),
				arlen(z), bits);
			DBG(drv->printbdd(wcout<<"subterm:"<<endl,r,bits,z,rel);)
			it = res.emplace(diff_t::key_type{rel, z}, F).first;
			it->second =
				bdd_or(it->second, bdd_and(*db.at({rel,z}),r));
			get_tree(rel, it->second, z, db, bits, res, done);
		}
	}
}

void get_tree(int_t rel, size_t root, ints ar, const db_t& db, size_t bits,
	diff_t& res) {
	set<size_t> done;
	get_tree(rel, root, ar, db, bits, res, done);
}
