#include "dnf.h"
#include <iostream>

clause::clause(const set<int>& s) : vector<int_t>(s.begin(), s.end()) {}

bool clause::has(int_t t) const {
	auto it = lower_bound(begin(), end(), t);
	return it != end() && *it == t;
}

void clause::add(int_t i) {
	if (empty()) push_back(i);
	else if (has(-i)) clear(), tau = false;
	else if (const_iterator it = lower_bound(begin(), end(), i); (it!=end() && *it!=i)
		|| (it = upper_bound(begin(), end(), i)) == end())
		insert(it, i);
}

void clause::del(int_t i) {
	const_iterator it = lower_bound(begin(), end(), i);
	if (it != end() && *it == i) erase(it);
	if (empty()) tau = true;
}

int_t clause::subclause(const clause& c) const {
	bool b = false;
	int_t r = -1;
	for (int_t i : c)
		if (!b && has(-i)) b = true, r = abs(i);
		else if (!has(i)) return 0;
	return r; 
}

pair<char, int_t> clause::subclause2(const clause& c) const {
	pair<char, int_t> ret;
	if (int_t r = subclause(c); r > 0 && size() == c.size()) ret = { 1, r };
	else if (r == -1) ret = { 1, 0 };
	else if ((r = c.subclause(*this)) > 0 && size() == c.size()) ret = { -1, r };
	else if (r == -1) ret = { -1, 0 };
	else ret = { 0, 0 };
	wcout << "subclause() this: " << *this << " c: " << c << " " << (int)ret.first << " " << ret.second << endl;
	return ret;
}

void dnf::add(clause&& c) {
	typedef pair<size_t, pair<char, int_t>> elem;
	if (c.tau) { clear(); tau = true; return; }
	if (c.empty()) return;
	vector<elem> m;
	vector<size_t> del;
	for (size_t n = 0; n < size(); ++n)
		if (auto r = c.subclause2(at(n)); !r.first) continue;
		else if (r.second) m.emplace_back(n, r);
		else if (r.first == 1) return;
		else del.push_back(n);
	if (m.empty()) { push_back(move(c)); return; }
	sort(m.begin(), m.end(), [this, c](const elem& x, const elem& y) {
		return ((x.second.first==1) ? at(x.first).size() :
			c.size()) > ((y.second.first==1) ? at(y.first).size() : c.size());
	});
	if (m[0].second.first > 0)
		c = move((*this)[m[0].first]), erase(begin() + m[0].first);
	c.del(m[0].second.second), c.del(-m[0].second.second);
	for (size_t i : del) erase(begin() + i);
	add(move(c));
}

clause& clause::operator*=(const clause& c) {
	for (int_t i : c) if (add(i); empty()) break;
	return *this;
}

dnf clause::operator-() const {
	dnf r;
	for (int_t i : *this) r += clause({i});
	return r;
}

dnf& dnf::operator+=(const dnf& d) { for (clause c : d) add(move(c)); return *this; }

dnf dnf::operator*(const dnf& d) {
	dnf r;
	for (clause x : *this) for (const clause& y : d) r += move(x *= y);
	return r;
}

clause clause::eq(const set<array<int_t, 3>>& e) const {
	struct cmp {
		bool operator()(const array<int_t, 3>& a, int_t i) const { return a[1]<i; }
		bool operator()(int_t i, const array<int_t, 3>& a) const { return i<a[0]; }
	} c;
	clause r;
	for (int_t i : *this) {
		auto er = equal_range(e.begin(), e.end(), i, c);
		for (; er.first != er.second; ++er.first)
			if (auto& t = *er.first; i >= t[0] && i < t[1]) {
				r.add(i > 0 ? i + t[3] : i - t[3]);
				break;
			}
		if (er.first != er.second) r.add(i);
	}
	return r;
}

dnf dnf::eq(const set<array<int_t, 3>>& e, const set<int_t>&) const {
	dnf r;
	for (const clause& c : *this) r.add(c.eq(e));
	return r;
}

wostream& operator<<(wostream& os, const clause& c) {
	os << L'(';
	for (int_t i : c) os << i << L' ';
	return os << L')';
}

wostream& operator<<(wostream& os, const dnf& d) {
	for (const clause& c : d) os << c;
	return os;
}

int main() {
	clause x({1,2});
	clause y({1,-2});
	clause z({-1});
	clause t({1,2,3});
	dnf f;
	wcout << x << endl;
	wcout << y << endl;
	wcout << z << endl;
	wcout << t << endl;
	f.add(move(x));
	wcout << "f1: " << f << endl;
	f.add(move(y));
	wcout << "f2: " << f << endl;
//	f.add(move(z));
//	wcout << "f3: " << f << endl;
	f.add(move(t));
	wcout << "f4: " << f << endl;
	return 0;
}
