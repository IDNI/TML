#include <vector>
#include <set>
#include <map>
#include <iostream>
#include <cstring>
#include <algorithm>
using namespace std;

typedef int32_t int_t;
typedef vector<int_t> term;
typedef vector<int_t> env;

int_t rep(env& e, int_t x) {
	return x > 0 ? x : e[-x-1] ? e [-x-1] = rep(e, e[-x-1]) : x;
}

int_t rep(const env& e, int_t x) {
	return x > 0 ? x : e[-x-1] ? rep(e, e[-x-1]) : x;
}

bool rep(env& e, int_t x, int_t y) {
	if ((x = rep(e, x)) == (y = rep(e, y))) return true;
	if (x > y) ::swap(x, y);
	return x > 0 ? x == y : (e[-x-1] = y, true);
}

bool rep(env& r, const env& e) {
	if (r.size() != e.size()) throw 0;
	for (size_t n = 0; n < r.size(); ++n)
		if (e[n] && !rep(r, n+1, e[n])) return false;
	return true;
}

ostream& operator<<(ostream& os, const env& e) {
	os << "{ ";
	for (int_t n = 0; n < (int_t)e.size(); ++n)
		if (e[n]) os << -n-1 << '=' << e[n] << ' ';
	return os << '}';
}

template<typename T>bool cmpsz(const T& x,const T& y){return x.size()<y.size();}

set<env> join(vector<set<env>>& v) {
	if (v.size() == 1) return v[0];
	sort(v.begin(), v.end(), cmpsz<set<env>>);
	set<env> r = v[0];
	for (size_t pos = 1; pos < v.size() - 1 && !r.empty(); ++pos)
		for (const env& x : r)
			for (const env& y : v[pos])
				if (env e(x.size()); rep(e, x) && rep(e, y))
					r.emplace(e);
	return r;
}

bool sub(const env& e, term& t) {
	for (size_t n=0; n<t.size(); ++n) if((t[n]=rep(e, t[n]))<0)return false;
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

void fwd(set<term>&facts, vector<vector<term>> negs, vector<vector<term>> poss){
	size_t n, k;
	vector<size_t> numvars(negs.size());
	map<int_t, size_t> varloc;
	vector<vector<set<env>>> matches(negs.size());

	auto sub_negs = [&negs, &matches, &n, &k, &numvars](const term& t) {
		if (t.size() != negs[n][k].size()) return;
		env e(numvars[n]);
		for (size_t j = 0; j < t.size(); ++j)
			if (!rep(e, t[j], rep(e, negs[n][k][j])))
				return;
		matches[n][k].emplace(move(e));
	};

	auto sub_poss = [&facts, &poss, &n](const env& e) {
		for (term t : poss[n]) if (sub(e, t)) facts.emplace(t);
	};

	for (n = 0; n < negs.size(); ++n)
		normvars(poss[n]), numvars[n] = normvars(negs[n]);

loop:	const size_t sz = facts.size();
	for (n = 0; n < negs.size(); ++n) {
		matches[n] = vector<set<env>>(negs[n].size());
		for (k = 0; k < negs[n].size(); ++k)
			for_each(facts.begin(), facts.end(), sub_negs);
		set<env> jmn = join(matches[n]);
		for_each(jmn.begin(), jmn.end(), sub_poss);
	}
	if (sz == facts.size()) return;
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
