#include <vector>
#include <set>
#include <map>
#include <iostream>
using namespace std;
typedef int32_t int_t;
typedef vector<int_t> term;

struct env : public map<int_t, int_t> {
	int_t rep(int_t x) {
		auto it = find(x);
		return it==end() ? x : emplace(x,rep(it->second)).first->second;
	}
	int_t rep(int_t x) const {
		auto it = find(x);
		return it == end() ? x : rep(it->second);
	}
	bool rep(int_t x, int_t y) {
		if ((x = rep(x)) == (y = rep(y))) return true;
		return x>0 && y>0 ? x==y : (emplace(min(x, y), max(x, y)),true);
	}
};
set<env> join(vector<set<env>> v, size_t pos = 0) { // TODO: sort by size
	if (pos == v.size() - 1) return v[v.size() - 1];
	env e;
	set<env> r, t = v[pos + 1];
	for (const env& x : v[pos])
		for (const env& y : v[pos + 1]) {
			e.clear();
			bool b = true;
			for (auto t:x) if(!(b&=e.rep(t.first, t.second)))break;
			if (!b) break;
			for (auto t:y) if(!(b&=e.rep(t.first, t.second)))break;
			if (b) r.emplace(e);
		}
	return v[pos + 1] = r, r = join(v, pos + 1), v[pos + 1] = t, r;
}
bool sub(const env& e, term& t) {
	for (size_t n=0; n<t.size(); ++n) if ((t[n]=e.rep(t[n]))<0)return false;
	return true;
}
void fwd(set<term>& f, vector<vector<term>> b, vector<vector<term>> h) {
	const size_t sz = f.size();
	size_t n = 0, k, j;
	bool p;
	vector<vector<set<env>>> m(b.size());
	for (env e; n < b.size(); ++n)
		for (m[n].resize(b[n].size()), k = 0; k < b[n].size(); ++k)
			for (const term& t : f) {
				if (t.size() != b[n][k].size()) continue;
				for (e.clear(), p=true, j=0; p&&j<t.size();++j)
					p &= e.rep(t[j], e.rep(b[n][k][j]));
				if (p) m[n][k].emplace(e);
			}
	for (n = 0; n < b.size(); ++n)
		for (const env& e : join(m[n]))
			for (term t : h[n]) if (sub(e, t)) f.emplace(t);
	if (sz == f.size()) return;
	fwd(f, b, h);
}
void print(ostream& os, const set<term>& s) {
	for (const term &t : s) {
		os << "( ";
		for (int_t i : t) os << i << ' ';
		os << ')';
	}
}
int main(int, char**) {
	// -1 1 -> -1 2
	// -1 1, -1 2 -> -1 3
	// 1 1
	// 2 1
	set<term> f = {{1,1},{2,1}};
	fwd(f,{{{-1,1}},{{-1,1},{-1,2}}},{{{-1,2}},{{-1,3}}});
	print(cout, f);
}
