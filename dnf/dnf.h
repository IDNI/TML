#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

using namespace std;
typedef int32_t int_t;
wostream& operator<<(wostream& os, const struct clause&);
wostream& operator<<(wostream& os, const struct dnf&);

struct clause : protected vector<int_t> {
	clause(){}
	clause(const set<int>& s);
	void add(int_t i);
	void del(int_t i);
	size_t size() const { return vector<int_t>::size(); }
	bool empty() const { return vector<int_t>::empty(); }
	bool has(int_t) const;
	friend wostream& operator<<(wostream& os, const clause&);
	int_t subclause(const clause& c) const;
	pair<char, int_t> subclause2(const clause& c) const;
};

struct dnf : protected vector<clause> {
	friend wostream& operator<<(wostream& os, const dnf&);
	bool tau; // whether tautology or unsat
	void add(clause&& c);
	size_t size() const { return vector<clause>::size(); }
	bool empty() const { return vector<clause>::empty(); }
};
