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

#define setbit(x, n) ((x) |= 1 << (n))
#define getbit(x, n) ((x) & (1 << (n)))

struct cmpterm {
	bool operator()(const int_t* x, const int_t* y) const {
		return *x == *y ? memcmp(x, y, sizeof(int_t)**x)<0 : (*x < *y);
	}
};

class table : protected dnf {
	const int_t* get(const clause& c, size_t len, size_t rel) {
		int_t* t = new int_t[len];
		*t = len;
		t[1] = rel;
		return t;
	}
	void get(const clause& c, set<const int_t*, cmpterm>& r) {
		size_t psz = 0, nsz = 0, n, z, k, len, rel, _z, _k, prel, nrel;
		for (n = 0; n < arbits; ++n)
			if (c.has(n+1)) setbit(psz, n);
			else if (c.has(-n-1)) setbit(nsz, n);
		const size_t m = (~(psz | nsz)) & ((1 << arbits)-1);
		for ((z = 1 << __builtin_popcount(m)), k=len=0; z--; k=len=0) {
			for (n = 0; n < arbits; ++n)
				if (psz & (1 << n)) setbit(len,n);
				else if (nsz & (1 << n)) continue;
				else setbit(len, getbit(z, k++));
			for (prel=nrel=0; n < rbits+arbits; ++n)
				if (c.has(n+1)) setbit(prel,n-arbits);
				else if (c.has(-n-1)) setbit(nrel,n-arbits);
			const size_t _m = (~(prel | nrel)) & ((1 << rbits)-1);
			for (_z=1<<__builtin_popcount(_m), _k=0, rel=0; _z--; _k=rel=0) {
				for (n = 0; n < rbits; ++n)
					if (prel & (1 << n)) setbit(rel, n);
					else if (nrel & (1 << n)) continue;
					else setbit(rel, getbit(_z, _k++));
				r.emplace(get(c, len, rel));
			}
		}
	}
public:
	const size_t ubits, rbits, arbits;
	table(size_t ubits, size_t rbits, size_t arbits) :
		ubits(ubits), rbits(rbits), arbits(arbits) {}
	void add(const int_t* t) {
		clause c;
		size_t v = 0;
		for (size_t n = 0; n < arbits; ++n)
			c.add(*t & (1 << n) ? -++v : ++v);
		for (size_t n = 0; n < rbits; ++n)
			c.add(t[1] & (1 << n) ? -++v : ++v);
		for (size_t k = 2; k < (size_t)*t; ++k)
			for (size_t n = 0; n < ubits; ++n)
				c.add(t[k] & (1 << n) ? -++v : ++v);
		dnf::add(move(c));
	}
	void get(set<const int_t*, cmpterm>& r) {
		for (const clause& c : *this) get(c, r);
	}
};
