#include "fwd.h"

using namespace std;

// union-find with path compression specialized for vars/consts
int_t rep(env& e, int_t x) { return x>0?x:e[-x-1]?e[-x-1]=rep(e, e[-x-1]):x; } 
int_t rep(const env& e, int_t x) { return x>0?x:e[-x-1]?rep(e,e[-x-1]):x; } 
bool rep(env& e, int_t x, int_t y) {
	if ((x = rep(e, x)) == (y = rep(e, y))) return true;
	if (x > y) ::swap(x, y);
	return x > 0 ? x == y : (e[-x-1] = y, true);
} 
bool rep(env& r, const env& e, size_t sz) {
//	if (r.size() != e.size()) throw 0;
	for (size_t n = 0; n < sz; ++n)
		if (e[n] && !rep(r, n+1, e[n])) return false;
	return true;
}
#define mkenv(sz) ((env)memset(alloca(sz * sizeof(int_t)), 0, sz * sizeof(int_t)))
#define dup(e, sz) (env)memcpy(new int_t[sz], e, sizeof(int_t) * sz)
// join all combinations of noncontradicting envs
set<env> join(vector<set<env>>& v, size_t nvars) {
	if (v.size() == 1) return v[0];
	sort(v.begin(), v.end(), [](const set<env>& x, const set<env>& y) {
		return x.size() < y.size(); });
	set<env> r = v[0];
	for (size_t pos = 1; pos < v.size() - 1 && !r.empty(); ++pos)
		for (const env& x : r)
			for (const env& y : v[pos])
				if (env e=mkenv(nvars); rep(e, x, nvars) && rep(e, y, nvars))
					r.emplace(dup(e, nvars));
	return r;
}
// normalize variable names to sequential order
size_t normvars(clause& t) {
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
// calc which positive term (head) may match which negative term (body)
void fwd::cache(size_t n, size_t k, size_t i, size_t j) {
	env e = mkenv(numvars[n]);
	for (size_t l = 0; l < poss[i][j].size(); ++l)
		if (!rep(e, poss[i][j][l], rep(e, negs[n][k][l])))
			return;
	p2n[pair(i, j)].emplace(n, k);
}
// given the clauses, normalize and calc the cache
fwd::fwd(vector<clause> negs, vector<clause> poss) :
	negs(negs), poss(poss), numvars(new size_t[negs.size()]),
	matches(negs.size()) {

	DEBUG(print_clauses());
	if (negs.size() != poss.size()) throw 0;
	for (size_t n = 0; n < negs.size(); ++n) {
		normvars(poss[n]), numvars[n] = normvars(negs[n]);
		for (size_t k = 0; k < negs[n].size(); ++k)
			for (size_t i = 0; i < poss.size(); ++i)
				for (size_t j = 0; j < poss[i].size(); ++j)
					cache(n, k, i, j);
	}
	DEBUG(print_matches());
}
// substitute a term in a negative literal, add the env to matches[] in success
void fwd::sub_negs(size_t n, size_t k, const term& t) {
	size_t j;
	if (t.size() != negs[n][k].size()) return;
	env e = mkenv(numvars[n]);
	for (j = 0; j < t.size(); ++j)
		if (!rep(e, t[j], rep(e, negs[n][k][j])))
			break;
	if (j == t.size()) matches[n][k].emplace(dup(e, numvars[n]));
}
// substitute successful negative literal's envs in their matching positives
void fwd::sub_poss(size_t n, size_t k, terms& facts, const env& e) {
	term t = poss[n][k];
	for (int_t &i : t) i = rep(e, i);
	facts.emplace(t);
	for (auto x : p2n[pair(n, k)]) {
		size_t i = get<0>(x), j = get<1>(x);
		set<env> s;
//		swap(s, matches[pair(i, j)]);
	}
}
// main function, loop until fixed point reached
void fwd::operator()(terms& facts) {
	size_t sz, n;
	while ((sz = facts.size())) {
		for (n = 0; n < negs.size(); ++n) {
			matches[n] = vector<set<env>>(negs[n].size());
			for (const term& t : facts)
				for (size_t k = 0; k < negs[n].size(); ++k)
					sub_negs(n, k, t);
		}
		for (n = 0; n < negs.size(); ++n)
			for (const env& e : join(matches[n], numvars[n]))
				for (size_t k = 0; k < poss[n].size(); ++k)
					sub_poss(n, k, facts, e);
		if (sz == facts.size()) return;
	}
}
