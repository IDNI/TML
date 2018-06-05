#include "dict.h"

static wostream& operator<<(wostream& os, const term& t) {
	for (auto x : t) os << dict(x) << L' ';
	return os;
}

static wostream& operator<<(wostream& os, const set<term>& s) {
	size_t sz = s.size();
	for (auto t : s) os << t << (--sz ? ", " : "");
	return os;
}

static int_t rep(const tmpenv& e, int_t x) {
	return x>0 || !e[-x-1] || e[-x-1] == x ? x : rep(e, e[-x-1]);
}

static int_t rep(tmpenv& e, int_t x){
	return x>0 || !e[-x-1] || e[-x-1] == x ? x : e[-x-1] = rep(e, e[-x-1]);
}

static bool rep(tmpenv& e, int_t x, int_t y) {
	if ((x = rep(e, x)) > (y = rep(e, y))) ::swap(x, y);
	return x == y || (x < 0 && (e[-x - 1] = y, true));
}

extern size_t unifications;

static bool unify(const term& x, const term& g, tmpenv e) {
	++unifications;
	debug_unify_begin;
	if (x.size() != g.size()) return false;
	for (size_t n=0; n<x.size(); ++n) if (!rep(e, x[n], g[n])) return false;
	debug_unify_pass;
	return true;
}

static term sub(const term& t, const tmpenv& e) {
	term r(t.size());
	debug_sub_begin;
	for (size_t n = 0; n < t.size(); ++n) r[n] = (t[n] ? rep(e, t[n]) : 0);
	debug_sub_end;
	return r;
}

static clause sub(const clause& t, const tmpenv e) {
	clause r;
	debug_sub_begin;
	for (const term& x : t) r.emplace(sub(x, e));
	debug_sub_end;
	return r;
}

static set<int_t> vars(const term& x) {
	set<int_t> r;
	for (int_t t : x) if (t < 0) r.emplace(t);
	return r;
}

static size_t nvars(const r2& t) {
	set<int_t> r;
	for (int_t t : t.first.first) if (t < 0) r.emplace(t);
	for (int_t t : t.first.second) if (t < 0) r.emplace(t);
	return r.size();
}

static term interpolate(const term& x, const term& y, int_t relid) {
	term r;
	r.push_back(relid);
	debug_interpolate_begin;
	set<int_t> vx = vars(x), vy = vars(y);
	for (auto ix = vx.begin(), iy = vy.begin(); ix != vx.end() && iy != vy.end();)
		if (*ix == *iy) r.push_back(*ix++), ++iy;
		else if (*ix < *iy) ++ix;
		else ++iy;
	debug_interpolate_end;
	return r;
}

static void normvars(term &t, size_t& k, map<int_t, int_t>& v) {
	for (int_t &i : t)
		if (i >= 0) continue;
		else if (auto it = v.find(i); it == v.end()) v.emplace(i, -++k);
		else i = it->second;
}

static void normvars(clause &c, size_t& k, map<int_t, int_t>& v) {
	clause r;
	for (term t : c) normvars(t, k, v), r.emplace(move(t));
	c = move(r);
}

static void normvars(clause &b, clause &h) {
	map<int_t, int_t> v;
	size_t k = 0;
	normvars(b, k, v);
	normvars(h, k, v);
}

static void normvars(term &t, clause &h) {
	map<int_t, int_t> v;
	size_t k = 0;
	normvars(t, k, v);
	normvars(h, k, v);
}

static void normvars(term &x, term& y, clause &h) {
	map<int_t, int_t> v;
	size_t k = 0;
	normvars(x, k, v);
	normvars(y, k, v);
	normvars(h, k, v);
}
