#include "dnf.h"
#include "pfp.h"

clause cempty;

clause& operator*=(clause &c, int_t x) {
	return has(c, -x) ? cempty : (c.emplace(x), c);
}

clause& operator*=(clause &d, const clause& c) {
	for (int_t x : c) if ((d *= x).empty()) return cempty;
	return d;
}

clause operator*(const clause &x, const clause& y) {
	clause r = x;
	return r *= y;
}

dnf& operator+=(dnf& d, const clause& c) { return c.empty() ? d : (d.emplace(c), d); }
dnf& operator-=(dnf& d, const clause& c) { return d.erase(c), d; }

dnf operator*(const dnf& x, const dnf& y) {
	dnf r;
	for (const clause& i : x) for (const clause& j : y) r += i * j;
	return r;
}

dnf& operator*=(dnf& x, const dnf& y) { return x = x * y; }

dnf& operator*=(dnf& x, const clause& y) { return x = x * dnf{ y }; }

dnf operator/(const dnf& d, const clause& c) {
	dnf r;
	for (auto it = d.begin(); it != d.end(); ++it) {
		clause t;
		for (int_t i : *it) if (has(c, i) || has(c, -i)) t.emplace(i);
		if (t.size() == c.size()) r.emplace(t);
	}
	return r;
}

dnf operator%(const dnf& d, const clause& c) {
	dnf r;
	for (auto it = d.begin(); it != d.end(); ++it) {
		clause t;
		for (int_t i : *it) if (!has(c, i) && !has(c, -i)) t.emplace(i);
		r += t;
	}
	return r;
}

clause rename(const clause& c, size_t from, size_t to, size_t offset) {
	clause r;
	for (int_t x : c)
		if ((size_t)abs(x) >= from && (size_t)abs(x) < to)
			r *= x < 0 ? x-offset : (x+offset);
		else if ((r *= x).empty()) return cempty;
	return r;
}

dnf rename(const dnf& d, size_t from, size_t to, size_t offset) {
	dnf r;
	for (const clause& c : d) r += rename(c, from, to, offset);
	return r;
}

clause from_bits(const int_t* t, size_t n, size_t offset, size_t bits) {
	assert(offset);
	clause r;
	int_t k = offset;
	for (; n--; ++t)
		for (size_t j=0; j < bits; ++j) r *= *t & (1 << j) ? k++ : -k++;
	return r;
}

wostream& operator<<(wostream& os, const clause& c) {
	for (auto it = c.begin();;) {
		os << *it;
		if (++it != c.end()) os << L','; else break;
	}
	return os;
}

wostream& operator<<(wostream& os, const dnf& d) {
	for (const clause& c : d) os << L'(' << c << L')';
	return os;
}

int main() {
	setlocale(LC_ALL, "");

	vector<int_t> x = { 2, -1, 2 };
	table t(1, 2, 1, -1);
	t += &x[0];
	wcout << t;
	return 0;
/*	int_t x = 4;
	//wcin >> x;
	dnf d = { { 1, -2, 3}, { 2, -3, x }};
	dnf e = { { 3}, { x }};
	wcout << d << endl << e << endl << d*e << endl;
	wcout << L"ren: " << endl << rename(d*e, 2, 3, 1) << endl;
	wcout << d << L" / { 3 } = " << d / clause{3} << endl;
	wcout << d << L" % { 3 } = " << d % clause{3} << endl;
	int_t p[] = { 3, 4 };
	wcout << L" from_bits({3,4},2,6,5) " << from_bits(p,2,6,5) << endl;
	return 0;*/
}
