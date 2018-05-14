#include <array>
#include <vector>
#include <set>
#include <map>
#include <variant>
#include <alloca.h>
#include <cstring>
#include <cassert>
#include <stdexcept>
#include <iostream>
#include <error.h>
using namespace std;
template<typename T> using two = pair<T, T>;
typedef int32_t int_t;
typedef vector<int_t> term;
typedef set<term> clause;
typedef set<term> terms;
typedef two<terms> rn;
typedef pair<two<term>, terms> r2;
typedef pair<term, terms> r1;
typedef int_t* tmpenv;

#define envclear(e, sz) ((tmpenv)memset((e),0,sz*sizeof(int_t)))
#define mkenv(sz) envclear(alloca(sz*sizeof(int_t)), sz)
#define dup(e, sz) env(e, &e[sz])

#define error(x) (wcerr<<(x)<<endl)
#define err_head_var_not_in_body \
error("Variables that appear on consequences must also appear in the premises")

#define debug_addxy \
	wcout << "add: " << x << " => " << y << endl
#define debug_addxyh \
	wcout << "add: " << x << ',' << y << " => " << h << endl
#define debug_unify_begin \
	wcout << "unifying: " << x << " with " << g << endl
#define debug_unify_pass \
	wcout << "passed with: " << e << endl
#define debug_sub_begin \
	wcout << "sub("<<t<<") = "
#define debug_sub_end \
	wcout << r << endl
#define debug_interpolate_begin \
	wcout << "interpolate: " << x << ',' << y
#define	debug_interpolate_end \
	wcout << " = " << r << endl

class dict_t {
	map<wstring, int_t> m;
	vector<wstring> v;
public:
	dict_t() { m.emplace(L"not", 0); }
	int_t operator()(const wstring& s) {
		assert(s.size());
		if (auto it = m.find(s); it != m.end()) return it->second;
		v.push_back(s);
		return m.emplace(s,s[0]==L'?'?-v.size():v.size()).first->second;
	}
	wstring operator()(int_t x) const {
		return x > 0 ? v[x - 1] : x ? L"v"s+to_wstring(-x) : L"not";
	}
	int_t tmp(wstring prefix = L"_") {
		wstring s;
		for (size_t n = 1;;++n) {
			wstring s = prefix + to_wstring(n);
			if (m.find(s) == m.end()) return (*this)(s);
		}
	}
} dict;

wostream& operator<<(wostream& os, const term& t) {
	for (auto x : t) os << dict(x) << L' ';
	return os;
}

wostream& operator<<(wostream& os, const set<term>& s) {
	size_t sz = s.size();
	for (auto t : s) os << t << (--sz ? ", " : "");
	return os;
}

int_t rep(const tmpenv& e, int_t x) {
	return x>0 || !e[-x-1] || e[-x-1] == x ? x : rep(e, e[-x-1]);
} 

int_t rep(tmpenv& e, int_t x){
	return x>0 || !e[-x-1] || e[-x-1] == x ? x : e[-x-1] = rep(e, e[-x-1]);
}

bool rep(tmpenv& e, int_t x, int_t y) {
	if ((x = rep(e, x)) > (y = rep(e, y))) ::swap(x, y);
	return x == y || (x < 0 && (e[-x - 1] = y, true));
} 

size_t unifications = 0;

bool unify(const term& x, const term& g, tmpenv e) {
	++unifications;
	debug_unify_begin;
	if (x.size() != g.size()) return false;
	for (size_t n=0; n<x.size(); ++n) if (!rep(e, x[n], g[n])) return false;
	debug_unify_pass;
	return true;
} 

term sub(const term& t, const tmpenv& e) {
	term r(t.size());
	debug_sub_begin;
	for (size_t n = 0; n < t.size(); ++n) r[n] = (t[n] ? rep(e, t[n]) : 0);
	debug_sub_end;
	return r;
}

terms sub(const terms& t, const tmpenv e) {
	terms r;
	debug_sub_begin;
	for (const term& x : t) r.emplace(sub(x, e));
	debug_sub_end;
	return r;
}

set<int_t> vars(const term& x) {
	set<int_t> r;
	for (int_t t : x) if (t < 0) r.emplace(t);
	return r;
}

size_t nvars(const r2& t) {
	set<int_t> r;
	for (int_t t : t.first.first) if (t < 0) r.emplace(t);
	for (int_t t : t.first.second) if (t < 0) r.emplace(t);
	return r.size();
}

term interpolate(const term& x, const term& y, int_t relid) {
	term r;
	r.push_back(relid);
	debug_interpolate_begin;
	set<int_t> vx = vars(x), vy = vars(y);
	for (	auto ix = vx.begin(), iy = vy.begin();
		ix != vx.end() && iy != vy.end();)
		if (*ix == *iy) r.push_back(*ix++), ++iy;
		else if (*ix < *iy) ++ix;
		else ++iy;
	debug_interpolate_end;
	return r;
}

r2 normvars(term x, term y, clause h) {
	debug_addxyh;
	map<int_t, int_t> v;
	size_t k = 0;
	clause hh;
	term tt;
	for (size_t n = 0; n < x.size(); ++n)
		if (x[n] >= 0) continue;
		else if (auto it = v.find(x[n]); it == v.end()) v.emplace(x[n], -++k);
		else x[n] = it->second;
	for (const term& t : h) {
		for (int_t& i : (tt = t))
			if (i >= 0) continue;
			else if (auto it = v.find(i); it == v.end()) err_head_var_not_in_body;
			else i = it->second;
		hh.emplace(move(tt));
	}
	return { { x, y }, hh } ;
}

int main() {
	set<rn> Rn;
	set<r2> R2;
	set<r1> R1;
	terms F;
	size_t arity = 0;

	for (auto r : Rn)
		for (;;)
			if (r.first.empty()) break; // safeguard
			else if (r.first.size() == 1) { R1.emplace(*r.first.begin(), r.second); break; }
			else {
				term x = *r.first.erase(r.first.begin()), y = *r.first.erase(r.first.begin());
				if (r.first.size() == 2) arity = max(arity, nvars(*R2.emplace(two<term>{x, y}, r.second).first));
				else arity = max(arity, nvars(*R2.emplace(normvars(x, y, { interpolate(x, y, dict.tmp()) })).first));
			}
	for (auto r : R2)
		for (auto f : F) {
			if (tmpenv e = mkenv(arity); unify(r.first.first, f, e))
				R1.emplace(sub(r.first.second, e), sub(r.second, e));
			if (tmpenv e = mkenv(arity); unify(r.first.second, f, e))
				R1.emplace(sub(r.first.first, e), sub(r.second, e));
		}
	bool b;
	do {
		b = false;
		for (auto r : R1)
			for (auto ff : F)
				if (tmpenv e = mkenv(arity); unify(r.first, ff, e)) {
					terms ff = sub(r.second, e);
					for (const term& f : ff)
						if (!F.emplace(f).second) continue;
						else for (auto r : R2) {
							if (tmpenv e = mkenv(arity); unify(r.first.first, f, e))
								b |= R1.emplace(sub(r.first.second, e), sub(r.second, e)).second;
							if (tmpenv e = mkenv(arity); unify(r.first.second, f, e))
								b |= R1.emplace(sub(r.first.first, e), sub(r.second, e)).second;
						}
				}
	} while (b);
	return 0;
}
