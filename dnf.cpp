#include <set>
#include <iostream>
using namespace std;
typedef int int_t;
typedef set<int_t> clause; // pos and neg bools
typedef set<clause> dnf;

clause& operator*=(clause &d, const clause& c) {
	for (int_t x : c)
		if (d.find(-x) == d.end()) d.emplace(x);
		else return d.clear(), d;
	return d;
}

clause operator*(const clause &x, const clause& y) {
	clause r = x;
	return r *= y;
}

dnf& operator+=(dnf& d, const clause& c) { return c.size() ? d.emplace(c), d : d; }

dnf operator*(const dnf& x, const dnf& y) {
	dnf r;
	for (const clause& i : x)
		for (const clause& j : y)
			r += i * j;
	return r;
}

dnf& operator*=(dnf& x, const dnf& y) { return x = x * y; }

dnf& operator*=(dnf& x, const clause& y) { return x = x * dnf{ y }; }

void rename(dnf& f, int_t x, int_t y) {
	set<clause> s;
	for (auto it = f.begin(); it != f.end(); ++it)
		if (it->find(x) == it->end()) {
			if (it->find(-x) == it->end()) {s.emplace(*it); continue; }// || it->find(-y) != it->end()) continue;
			else if (it->find(y) == it->end()) {
				clause c = *it;
				c.erase(-x), c.emplace(-y), s.emplace(c);
			}
		}// else if (it->find(y) != it->end()) continue;
		else if (it->find(-y) == it->end()) {
			clause c = *it;
			c.erase(x), c.emplace(y), s.emplace(c);
		}
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
	dnf d = { { 1, -2, 3}, { 2, -3, 4 }};
	dnf e = { { 3}, { 4 }};
	wcout << d << endl;
	wcout << e << endl;
	wcout << d*e << endl;
	dnf p = d * e;
	rename(p, 2, -3);
	wcout << L"ren: " << endl << p << endl;
	return 0;
}
