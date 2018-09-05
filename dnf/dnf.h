#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <cstring>
#include <iostream>

using namespace std;
typedef int32_t int_t;
wostream& operator<<(wostream& os, const struct clause&);
wostream& operator<<(wostream& os, const struct dnf&);

struct clause : protected vector<int_t> {
	clause(){}
	clause(const set<int>& s);
	bool tau = false; // whether tautology or unsat

	void add(int_t i);
	void del(int_t i);
	int_t subclause(const clause& c) const;
	pair<char, int_t> subclause2(const clause& c) const;
	clause& operator*=(const clause& c);
	dnf operator-() const;
	clause eq(int_t x, int_t y) const;

	size_t size() const { return vector<int_t>::size(); }
	bool empty() const { return vector<int_t>::empty(); }
	bool has(int_t) const;
	friend wostream& operator<<(wostream& os, const clause&);
};

struct dnf : protected vector<clause> {
	dnf(){}
	dnf(clause&& c) { add(move(c)); }
	bool tau = false;

	// to optimize by keeping a map from pairs of vars to sets of clauses
	void add(clause&& c); 
	dnf& operator+=(const dnf& d);
	dnf operator*(const dnf& d);
	dnf eq(int_t x, int_t y);

	size_t size() const { return vector<clause>::size(); }
	bool empty() const { return vector<clause>::empty(); }
	friend wostream& operator<<(wostream& os, const dnf&);
};
