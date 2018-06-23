#include <vector>
#include <algorithm>
#include <iostream>
using namespace std;

typedef int32_t int_t;

struct term {
	vector<int_t> c;
	size_t v;
	term(){}
	term(const vector<int_t> &c, size_t v) : c(c), v(v) {}
};

ostream& operator<<(ostream& os, const term& t) {
	for (int_t i : t.c) os << i << ' ';
	return os << " + " << t.v;
}

bool unify(const term& x, const term& y, term& r) {
	cout << "x: " << x << endl << "y: " << y << endl;
	if (x.v+x.c.size() != y.v+y.c.size()) return false;
	size_t n, k, s, xv = x.v, yv = y.v;
	for (n = k = s = 0; n < x.c.size() && k < y.c.size();)
		if (x.c[n] < y.c[k]) { if (++n, !yv--) return false; }
		else if (x.c[n] > y.c[k]) { if (++k, !xv--) return false; }
		else ++n, ++k, ++s;
	r.c.resize(x.c.size() + y.c.size() - s);
	set_union(x.c.begin(), x.c.end(), y.c.begin(), y.c.end(), r.c.begin());
	return r.v = min(xv, yv), true;
}

int main() {
	term t;
	bool b = unify(term({1, 2, 3}, 3), term({2, 3, 4, 5}, 2), t);
	cout << t << endl;
	return 0;
}
