#include <vector>
#include <set>
#include <map>
#include <iostream>
#include <cstring>
#include <algorithm>
using namespace std;
typedef int32_t int_t;
typedef vector<int_t> term;

struct env : public vector<int_t> {
	typedef vector<int_t> base;
	env(size_t nvars) : base(nvars) {}
	int_t rep(int_t x) { return x>0?x:at(-x-1)?at(-x-1)=rep(at(-x-1)): x; }
	int_t rep(int_t x) const{ return x>0 ? x : at(-x-1)?rep(at(-x-1)): x; }
	bool rep(int_t x, int_t y) {
		if ((x = rep(x)) == (y = rep(y))) return true;
		if (x > y) ::swap(x, y);
		return x > 0 ? x == y : (at(-x-1) = y, true);
	}
	bool rep(const env& e) {
		if (size() != e.size()) throw 0;
		for (size_t n = 0; n < size(); ++n)
			if (e[n] && !rep(n+1, e[n]))
				return false;
		return true;
	}
	size_t size() const { return base::size(); }
	void clear() { size_t s = size(); base::clear(), resize(s); }
	bool operator<(const env& e) const { return (*(base*)(this))<(base)e; }
	void print(ostream& os) const {
		os << "{ ";
		for (int_t n = 0; n < (int_t)size(); ++n)
			if (at(n)) os << -n-1 << '=' << at(n) << ' ';
		os << '}';
	}
};
template<typename T>bool cmpsz(const T& x,const T& y){return x.size()<y.size();}
set<env> join(vector<set<env>>& v) {
	if (v.size() == 1) return v[0];
	stable_sort(v.begin(), v.end(), cmpsz<set<env>>);
	set<env> r = v[0];
	for (size_t pos = 1; pos < v.size() - 1 && !r.empty(); ++pos)
		for (const env& x : r)
			for (const env& y : v[pos])
				if (env e(x.size()); e.rep(x) && e.rep(y))
					r.emplace(e);
	return r;
}
bool sub(const env& e, term& t) {
	for (size_t n=0; n<t.size(); ++n) if((t[n]=e.rep(t[n]))<0) return false;
	return true;
}
size_t normvars(vector<term>& t) {
	map<int_t, size_t> v;
	size_t k = 0, j, nv = 1;
	for (; k < t.size(); ++k)
		for (j = 0; j < t[k].size(); ++j)
			if (t[k][j] > 0) continue;
			else if (auto it = v.find(t[k][j]); it == v.end())
				v.emplace(t[k][j], nv), t[k][j] = -nv++;
			else t[k][j] = t[k][it->second - 1];
	return nv - 1;
}
void fwd(set<term>& f, vector<vector<term>> b, vector<vector<term>> h) {
	size_t n, k, j;
	bool p;
	vector<size_t> nv(b.size());
	map<int_t, size_t> v;
	vector<vector<set<env>>> m(b.size());
	for (n = 0; n < b.size(); ++n) normvars(h[n]), nv[n] = normvars(b[n]);
loop:	const size_t sz = f.size();
	for (n = 0; n < b.size(); ++n)
		for (m[n]=vector<set<env>>(b[n].size()), k=0; k<b[n].size();++k)
			for (const term& t : f) {
				if (t.size() != b[n][k].size()) continue;
				env e(nv[n]);
				for (p = true, j = 0; p && j < t.size(); ++j)
					p &= e.rep(t[j], e.rep(b[n][k][j]));
				if (p) m[n][k].emplace(move(e));
			}
	for (n = 0; n < b.size(); ++n) {
		for (const env& e : join(m[n]))
			for (term t : h[n])
				if (sub(e, t))
					f.emplace(t);
	}
	if (sz == f.size()) return;
	goto loop;
}
void print(ostream& os, const set<term>& s) {
	for (const term &t : s) {
		os << "( ";
		for (int_t i : t) os << i << ' ';
		os << ')';
	}
}
int main(int, char**) {
	// -1 1 -1 -> -1 -2
	// -1 -2, -1 2 -> -1 3
	// 1 1 1
	// 2 1 1
	set<term> f = {{1,1,1},{2,1,1}};
	fwd(f,{{{-1,1,-1}},{{-1,-2},{-1,2}}},{{{-1,2}},{{-1,3}}});
	print(cout, f);
}
