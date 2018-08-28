#include <set>
#include <map>
#include <cstdlib>
#include <iostream>
using namespace std;

typedef int int_t;
typedef set<int_t> clause; // pos and neg bools
typedef set<clause> dnf;

clause& operator+=(clause &c, int_t x); // append lit to clause. may return the empty clause
clause& operator*=(clause &d, const clause& c); // append clause to clause
clause operator*(const clause &x, const clause& y);
dnf& operator+=(dnf& d, const clause& c);  // add a clause to a formula
dnf operator*(const dnf& x, const dnf& y); // conjunction of formulas
dnf& operator*=(dnf& x, const dnf& y);
dnf& operator*=(dnf& x, const clause& y); // conjunct a formula vs a clause
dnf operator/(const dnf& d, const clause& c); // project only the occurences of the vars in c
dnf operator%(const dnf& d, const clause& c); // the complement of the above
clause rename(const clause& c, size_t from, size_t to, size_t offset); // rename vars
dnf rename(const dnf& d, size_t from, size_t to, size_t offset);
wostream& operator<<(wostream& os, const clause& c); // io
wostream& operator<<(wostream& os, const dnf& d);
