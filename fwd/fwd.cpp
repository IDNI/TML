#include "repl.h"

dict_t dict;
size_t unifications = 0;

static wostream& operator<<(wostream& os, const term& t) {
	for (auto x : t) os << dict(x) << L' ';
	return os;
}

static wostream& operator<<(wostream& os, const set<term>& s) {
	size_t sz = s.size();
	for (auto t : s) os << t << (--sz ? ", " : "");
	return os;
}
/*
static wostream& operator<<(wostream& os, const pair<term, clause>& t) {
	return os << t.first << " => " << t.second;
}
*/
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
	for (size_t n=0; n<x.size(); ++n)
		if (!rep(e, x[n], g[n]))
			return false;
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
/*
static void normvars(clause &b, clause &h) {
	map<int_t, int_t> v;
	size_t k = 0;
	normvars(b, k, v);
	normvars(h, k, v);
}
*/
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

bool fwd::add1rule(term b, clause h) {
	normvars(b, h);
	wcout << "added to R1: " << b << " => " << h << endl;
	return R1.emplace(b, h).second;
}

void fwd::add2rule(term x, term y, clause h) {
	wcout << "add2rule: " << x << ' ' << y << " => " << h << endl;
	normvars(x, y, h);
	for (auto f : F) r22r1(x, y, h, f);
	R2.emplace(r2{{x, y}, h}), arity = max(arity, nvars({{x,y},h}));
}

void fwd::add(const term& t) { wcout << "add fact: " << t << endl; add_fact(t); }
#define pop(x) *x.erase(x.begin())

void fwd::addrule(clause b, const clause& h) {
loop:	wcout << "add rule: " << b << " => " << h << endl;
	if (b.empty()) return;
	if (b.size() == 1) 
		if (add1rule(*b.begin(), h)) {
			r12r2(*b.begin(), h);
			return;
		}
	term x = *b.begin();
	b.erase(*b.begin());
	term y = *b.begin();
	b.erase(*b.begin());
	if (!b.empty()) {
		term i = interpolate(x, y, dict.tmp());
		b.emplace(i), add2rule(x, y, {i});
		goto loop;
	} else add2rule(x, y, h);
}


void fwd::r22r1(const term& x, const term& y, const clause& h, const term& f) {
	wcout << "r22r1: " << x << ' ' << y << " => " << h << " vs " << f << endl;
	tmpenv e = mkenv(arity);
	if (unify(x, f, e)) add1rule(sub(y, e), sub(h, e));
	if (envclear(e, arity), unify(y, f, e)) add1rule(sub(x, e), sub(h, e));
}

void fwd::r12r2(const term &b, const clause& h) {
	wcout << "r12r2: " << b << " => " << h << endl;
	tmpenv e = mkenv(arity);
	for (const term& f : F)
		if (envclear(e, arity), unify(b, f, e))
			for (const term& ff : sub(h, e))
				add_fact(ff);
}

void fwd::add_fact(const term& f) {
	wcout << "add fact: " << f << endl;
	if (!F.emplace(f).second) return;
	tmpenv e = mkenv(arity);
	for (const auto[b,h] : R1) r12r2(b, h);
	for (auto r : R2) {
		if (envclear(e, arity), unify(r.first.first, f, e)) {
			term b = sub(r.first.second, e);
			clause h = sub(r.second, e);
			if (add1rule(b, h)) r12r2(b, h);
		}
		if (envclear(e, arity), unify(r.first.second, f, e)) {
			term b = sub(r.first.first, e);
			clause h = sub(r.second, e);
			if (add1rule(b, h)) r12r2(b, h);
		}
	}
}
