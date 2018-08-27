#include <set>
#include <map>
#include <cstdlib>
#include <iostream>
using namespace std;
typedef int int_t;
typedef set<int_t> clause; // pos and neg bools
typedef set<clause> dnf;
#define has(x,y) ((x).find(y) != (x).end())
clause cempty;
clause& operator+=(clause &c, int_t x) {
	return has(c, -x) ? cempty : (c.emplace(x), c);
}
clause& operator*=(clause &d, const clause& c) {
	for (int_t x : c) if ((d += x).empty()) return cempty;
	return d;
}
clause operator*(const clause &x, const clause& y) {
	clause r = x;
	return r *= y;
}
dnf& operator+=(dnf& d, const clause& c) { return c.empty() ? d : (d.emplace(c), d); }
dnf operator*(const dnf& x, const dnf& y) {
	dnf r;
	for (const clause& i : x)
		for (const clause& j : y)
			r += i * j;
	return r;
}
dnf& operator*=(dnf& x, const dnf& y) { return x = x * y; }
dnf& operator*=(dnf& x, const clause& y) { return x = x * dnf{ y }; }
dnf operator/(const dnf& d, const clause& c) {
	dnf r;
	for (auto it = d.begin(); it != d.end(); ++it) {
		clause t;
		for (int_t i : *it)
			if (has(c, i) || has(c, -i)) t.emplace(i);
		if (t.size() == c.size()) r.emplace(t);
	}
	return r;
}
clause rename(const clause& c, size_t from, size_t to, size_t offset) {
	clause r;
	for (int_t x : c)
		if ((size_t)abs(x) >= from && (size_t)abs(x) < to) r += x < 0 ? x-offset : (x+offset);
		else r += x;
	return r;
}
dnf rename(const dnf& d, size_t from, size_t to, size_t offset) {
	dnf r;
	for (const clause& c : d) r.emplace(rename(c, from, to, offset));
	return r;
}
clause rename(const clause& c, map<int_t, int_t> s) {
	clause r;
	for (int_t x : c)
		if (auto it = s.find(x); it == s.end()) {
			if (auto jt = s.find(-x); jt == s.end()) r += x;
			else r += -jt->second;
		} else r += it->second;
	return r;
}
// hmm is possible to update the joined dnf (unlike the selection dnf)
// only upon deletion. and maybe the negated part upon addition.

// so TODO, aside offset rename, is to create a struct rule that takes
// care of binarization and the selectiomn and join dnfs given a db dnf. the rule is notified
// and updates upon h2b event.
// for deletion also need the "override-AND" operator.
// deletion is a matter of a clause being a subset of another it seems.
void rename(dnf& f, int_t x, int_t y) {
	clause c;
	set<clause> s;
	for (auto it = f.begin(); it != f.end(); ++it)
		if (!has(*it, x)) {
			if (!has(*it, -x)) s.emplace(*it);
			else if (!has(*it, y)) (c = *it).erase(-x), c.emplace(-y), s.emplace(c);
		} else if (!has(*it, -y)) (c = *it).erase(x), c.emplace(y), s.emplace(c);
	f = move(s);
}

wostream& operator<<(wostream& os, const clause& c) {
	for (int_t x : c) os << x << L'\t';
	return os;
}
wostream& operator<<(wostream& os, const dnf& d) {
	for (const clause& c : d) os << c << endl;
	return os;
}

int main() {
	setlocale(LC_ALL, "");
	int_t x = 4;
	wcin >> x;
	dnf d = { { 1, -2, 3}, { 2, -3, x }};
	dnf e = { { 3}, { x }};
	wcout << d << endl;
	wcout << e << endl;
	wcout << d*e << endl;
	dnf p = d * e;
	rename(p, 2, -3);
	wcout << L"ren: " << endl << p << endl;
	return 0;
}
