#include <iostream>
#include <cstdlib>
#include <string>
#include <sstream>
#include <cassert>
#include <vector>
#include <cctype>
#include <set>
#include <fstream>
using namespace std;

string fname(std::tmpnam(0));
ofstream out(fname.c_str());

char rand_rel(size_t rmax) { return 'a' + rand()%rmax; }
char rand_var(size_t vmax) { return 'A' + rand()%vmax; }
char rand_sym(size_t umax) { return '0' + rand()%umax; }

string rand_term(size_t len, size_t amax, size_t umax, size_t vmax, size_t rmax) {
	stringstream ss;
	assert(len);
	ss << rand_rel(rmax);
	for (size_t n = 0; n != len; ++n)
		ss << (random()&1 && vmax ? rand_var(vmax) : rand_sym(umax));
	string s = ss.str();
	return s;
}

void print_term(string t) {
	out << t[0] << '(';
	if (t.size() == 1) out << ')';
	else for (size_t n = 1; n != t.size(); ++n) {
		if (isupper(t[n])) out << '?';
		out << t[n];
		if (n != t.size()-1) out << " ";
		else out << ')';
	}
}

void print_rule(vector<string> r) {
	print_term(r[0]);
	if (r.size() == 1) { out << '.' << endl; return; }
	out << " :- ";
	for (size_t n = 1; n != r.size(); ++n) {
		print_term(r[n]);
		if (n == r.size() - 1) out<<'.'<<endl;
		else out << ',';
	}
}

vector<string> rand_rule(size_t bmax, size_t amax, size_t umax, size_t vmax, size_t rmax) {
	vector<string> r;
	vector<int> l;
	for (size_t n = 0; n != bmax+1; ++n) l.push_back((random()%amax)+1);
	for (size_t n = 0; n != bmax+1; ++n)
		r.push_back(rand_term(l[n], amax, umax, vmax, rmax));
	return r;
}

void print_query(string h) {
	out << "dump(" << h[0] << "(";
	for (size_t n = 1; n != h.size(); ++n) {
		out << '_';//(char)('A' + n);
		if (n == h.size() - 1) out << ")), ";
		else out << ", ";
	}
}

int main() {
	srand(time(0));
	set<vector<string>> s;
	size_t max_bodies = 3, max_arity = 4, max_universe = 5,
	       max_vars = 4, max_rels = 3, nfacts = 3, nrules = 3;
	for (size_t n = 0; n != nfacts; ++n)
		s.insert(rand_rule(0, max_arity, max_universe, 0, max_rels));
	for (size_t n = 0; n != nrules; ++n)
		s.insert(rand_rule(max_bodies, max_arity, max_universe,
			max_vars, max_rels));
	for (auto x : s) print_rule(x);
	cout << fname << endl;
	return 0;
}
