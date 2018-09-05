#include <vector>
#include <set>
#include <map>
#include <array>
#include <algorithm>
#include <cstring>
#include <iostream>

using namespace std;
typedef int32_t int_t;
wostream& operator<<(wostream& os, const struct clause&);
wostream& operator<<(wostream& os, const struct dnf&);

struct clause : protected vector<int_t> {
	friend class powdnf;
	clause(){}
	clause(const set<int>& s);
	size_t offset = 0;
	bool tau = false; // whether tautology or unsat

	void add(int_t i);
	void del(int_t i);
	int_t subclause(const clause& c) const;
	pair<char, int_t> subclause2(const clause& c) const;
	clause& operator*=(const clause& c);
	dnf operator-() const;
	clause& operator/=(const set<int_t>&);
	clause eq(const set<array<int_t, 3>>&, const set<int_t>&) const;

	size_t size() const { return vector<int_t>::size(); }
	bool empty() const { return vector<int_t>::empty(); }
	bool has(int_t) const;
	friend wostream& operator<<(wostream& os, const clause&);
};

struct dnf : protected vector<clause> {
	friend class powdnf;
	dnf(){}
	dnf(const dnf&& d) : vector<clause>(move(d)) {}
	dnf(clause&& c) { add(move(c)); }
	bool tau = false;

	// to optimize by keeping a map from pairs of vars to sets of clauses
	void add(clause&& c); 
	dnf& operator+=(const dnf& d);
	dnf operator*(const dnf& d);
	dnf eq(const set<array<int_t, 3>>&, const set<int_t>&) const;

	size_t size() const { return vector<clause>::size(); }
	bool empty() const { return vector<clause>::empty(); }
	friend wostream& operator<<(wostream& os, const dnf&);
};

#define clause_nvars(c) ((c).empty() ? 0 : max(abs(*(c).begin()), abs(*(c).rbegin())))

struct powdnf {
	const size_t k;
	dnf& f;
	const set<array<int_t, 3>> eqs;
	const set<int_t> vals, vars;
	powdnf(	size_t k, dnf& f, const set<array<int_t, 3>>& eqs,
		const set<int_t>& vals, const set<int_t>& vars) :
		k(k), f(f), eqs(eqs), vals(vals), vars(vars) {}
	void eq(vector<size_t>&& b, dnf& r) {
		clause c;
		size_t v = 0;
		for (size_t i : b) {
			if (v) f[i].offset = v, v += clause_nvars(f[i]);
			else v = clause_nvars(f[i]);
			c *= f[i];
		}
		r += move(c *= move(c.eq(eqs, vals) /= vars));
	}
};
