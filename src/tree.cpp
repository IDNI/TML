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
#include <sstream>
#include "lp.h"
#include "driver.h"
using namespace std;

#define un_mknum(x) (int_t(x))

bool operator<(const db_t::const_iterator& x, const db_t::const_iterator& y) {
	return	x->first != y->first ? x->first < y->first :
		x->second != y->second ? x->second < y->second : false;
}

bool operator<(const set<term>::const_iterator& x,
	const set<term>::const_iterator& y) { return *x < *y; }

bool ar_prefix(ints x, ints y) {
	if (!x[0]) x.erase(x.begin());
	if (!y[0]) y.erase(y.begin());
	if (y.size() < x.size()) return false;
	for (size_t n = 0; n < x.size(); ++n) if (x[n] != y[n]) return false;
	return true;
}

set<db_t::const_iterator> lp::tree_prefix(const prefix& p) const {
	set<db_t::const_iterator> r;
	for (auto it = db.lower_bound({p.rel,{}}); it->first.rel == p.rel; ++it)
		if (ar_prefix(p.ar, it->first.ar)) r.insert(it);
	return r;
}

void lp::get_tree(const prefix& p, spbdd root, db_t& out, set<spbdd>& done){
	if (root->leaf() && !root->trueleaf()) return;
	if (!done.emplace(root).second) return;
	db_t::iterator it;
	for (const pair<ints, array<size_t, 2>>& x : p.subterms())
		for (const db_t::const_iterator& y:tree_prefix({p.rel,x.first}))
			it = out.emplace(y->first,F).first,
			get_tree(y->first, it->second = it->second || (
				y->second && bdd_subterm(root,
				x.second[0], x.second[1], p.len(),
				y->first.len(), rng.bits)), out, done);
}

void lp::get_trees(const db_t& in, db_t& out) {
	set<spbdd> done;
	for (auto x : in)
		for (const db_t::const_iterator& it : tree_prefix(x.first))
			get_tree(it->first, it->second && bdd_expand(
				x.second, x.first.len(), it->first.len(),
				rng.bits), out, done), done.clear();
}

void lp::get_trees() {
	get_trees(trees, trees_out);
	for (auto x : strtrees) get_trees(x.second, strtrees_out[x.first]);
	auto it = db.end();
	for (auto x : trees_out) {
		if ((it = db.find(x.first)) == db.end())
			it = db.emplace(x.first, F).first;
		it->second = x.second;
	}
}

void driver::get_trees(wostream& os, const term& root,
	const map<term, vector<term>>& m, set<term>& done) {
	if (!done.emplace(root).second) return;
	// D: TODO: this will no longer work (>>2), we need a corresponding bm /type
	for (int_t i : root.args())
		if (i & 1) os << (wchar_t)un_mknum(i);
		else if (i & 2) os << (int_t)un_mknum(i);
		else if ((size_t)un_mknum(i) < dict.nsyms()) os << dict.get_sym(i);
		else os << L'[' << un_mknum(i) << L']';
	auto it = m.find(root);
	if (it == m.end()) return;
	for (auto x : it->second) get_trees(os, x, m, done);
}

wstring driver::get_trees(const term& root, const db_t& t, size_t bits) {
	set<term> s, done;
	map<term, vector<term>> m;
	for (auto x : t)
		from_bits(x.second, bits, x.first, [&s](const term& t) {
				s.insert(t); });
	for (const term& x : s) {
		const term r = x.root();
		for (const term& y : x.subterms()) m[r].push_back(y);
	}

	wstringstream ss;
	return get_trees(ss, root, m, done), ss.str();
//	o::out() << L"get_trees: " << ss.str() << endl;
}
