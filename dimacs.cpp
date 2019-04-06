// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.
#include "bdd.h"
#include <sstream>
#include <cmath>
using namespace std;

string trim(string s) {
	string r;
	size_t start = 0, end = s.size() - 1;
	while (isspace(s[start])) --start;
	while (isspace(s[end])) --end;
	return string(s.begin() + start, s.begin() + end);
}

ostream& operator<<(ostream& os, const bools& x) {
	for (auto y:x) os << (y?1:0);
	return os;
}

ostream& operator<<(ostream& os, const vbools& x) {
	for (auto y:x) os << y << endl;
	return os;
}

int main() {
	bdd_init();
	vector<vector<int>> p;
	for (string line; getline(cin, line);)
		if (line = trim(line), line[0] == 'c') continue;
		else if (line[0] == 'p') continue;
		else {
			stringstream ss;
			ss << line;
			int i;
			vector<int> v;
			while (ss >> i) if (i) v.push_back(i);
			p.push_back(v);
		}
	for (auto x : p) {
		for (int i : x) cout << i << ' ';
		cout << 0 << endl;
	}
	vector<size_t> v;
	int nvars = 0;
	size_t r = T;
	for (auto x : p) {
		size_t t = F;
		for (int i : x) {
			nvars = max(nvars, abs(i));
			t = bdd_or(t, from_bit(abs(i)-1, i>0));
		}
//		r = bdd_and(r, t);
		v.push_back(t);
	}
//	if (r == F) cout << "unsat" << endl;
//	else cout << "sat" << endl;
	if (bdd_and_many(v) == F) cout << "unsat" << endl;
	else cout << "sat" << endl;
	return 0;
}
