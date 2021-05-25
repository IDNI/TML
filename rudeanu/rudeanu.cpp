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
#include <cassert>
#include <vector>
#include <iostream>
#include "../src/bdd.h"

using namespace std;

typedef const char* ccp;

struct node {
	string s;
	vector<node*> v;
	node(ccp from, ccp to) {
		while (isspace(*from)) ++from;
		while (isspace(*to)) --to;
		s = string(from, to);
	}
	void add(node* n) { if (n) v.push_back(n); }
};

node* parse(ccp *s) {
	ccp t = *s;
	while (*t && *t != '(' && *t != ')' && *t != ',') ++t;
	if (t == *s) return 0;
	node *n = new node(*s, t);
	if (*(*s = t) == '(')
		do { ++*s, n->add(parse(s)); } while (**s == ',');
	return n;
}

void validate(ccp s) {
	size_t dep = 0;
	for (; *s; ++s)
		if (*s == '(') ++dep;
		else if (*s == ')' && !dep--)
			throw runtime_error("unbalanced parenthesis");
	if (dep) throw runtime_error("unbalanced parenthesis");
}

node* parse(ccp s) { return validate(s), parse(&s); }

ostream& operator<<(ostream& os, const node& n) {
	os << n.s;
	if (n.v.size()) {
		os << '(' << *n.v[0];
		for (size_t k = 1; k != n.v.size(); ++k) os << ',' << *n.v[k];
		os << ')';
	}
	return os;
}

spbdd_handle get_bf(const node* n) {
	if (n->s == "and") {
		bdd_handles v;
		for (const node* t : n->v) v.push_back(get_bf(t));
		return bdd_and_many(v);
	}
	if (n->s == "or") {
		bdd_handles v;
		for (const node* t : n->v) v.push_back(get_bf(t));
		return bdd_or_many(v);
	}
	if (n->s == "not") {
		if (n->v.size() != 1)
			throw runtime_error("not() takes exactly one argument");
		return htrue % get_bf(n->v[0]);
	}
	if (n->s == "T") return htrue;
	if (n->s == "F") return hfalse;
	try {
		int_t v = stoi(n->s);
		if (v <= 0)
			throw runtime_error("vars need to be positive integers");
		return from_bit(v - 1, true);
	} catch (...) { }
	throw runtime_error(string("unidentified: ") + n->s);
}

int main() {
	bdd::init();
	node *n = parse("and(1,2,or(3,not(4)))");
	cout << *n << endl;
	out<char>(cout, get_bf(n)) << endl;
}
