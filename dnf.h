#include <set>
#include <map>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <vector>
using namespace std;

typedef int int_t;
typedef set<int_t> clause; // pos and neg bools
typedef set<clause> dnf;

struct table {
	const size_t cols, bits, offset;
	const int_t rel;
	dnf f;
	table(size_t cols, size_t bits, size_t offset, int_t rel);
	table& operator+=(const int_t* t);
	table& operator-=(const int_t* t);
	vector<const int_t*> from_bits(const clause& c) const;
};

wostream& operator<<(wostream& os, const table& t);
clause& operator+=(clause &c, int_t x); // append lit to clause. may return the empty clause
clause& operator*=(clause &d, const clause& c); // append clause to clause
clause operator*(const clause &x, const clause& y);
dnf& operator+=(dnf& d, const clause& c);  // add a clause to a formula
dnf& operator-=(dnf& d, const clause& c);
dnf operator*(const dnf& x, const dnf& y); // conjunction of formulas
dnf& operator*=(dnf& x, const dnf& y);
dnf& operator*=(dnf& x, const clause& y); // conjunct a formula vs a clause
dnf operator/(const dnf& d, const clause& c); // project only the occurences of the vars in c
dnf operator%(const dnf& d, const clause& c); // the complement of the above
clause rename(const clause& c, size_t from, size_t to, size_t offset); // rename vars
dnf rename(const dnf& d, size_t from, size_t to, size_t offset);
clause from_bits(const int_t* t, size_t n, size_t offset, size_t bits);
wostream& operator<<(wostream& os, const clause& c); // io
wostream& operator<<(wostream& os, const dnf& d);

#define has(x,y) ((x).find(y) != (x).end())
#define bit_get(a, n, w) ((a)[(n)/(w)] & (1 << ((n)%(w))))
#define bit_set(a, n, w) ((a)[(n)/(w)] |= 1 << ((n)%(w)))
#define bit_unset(a, n, w) ((a)[(n)/(w)] &= ((1 << bits) - 1) - (1 << ((n)%(w))))
