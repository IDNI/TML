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
	node(const string &s) : s(s) {}
	node(const string &s, vector<node*> v) : s(s), v(v) {}
	void add(node* n) { if (n) v.push_back(n); }
} top("T"), bot("F");

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

node* node_neg(node* n) {
	if (n == &top) return &bot;
	if (n == &bot) return &top;
	return new node("not", {n});
}

node* node_and(node* x, node *y) {
	if (x == &bot) return &bot;
	if (y == &bot) return &bot;
	if (x == &top) return y;
	if (y == &top) return x;
	return new node("and", {x, y});
}

node* node_xor(node* x, node *y) {
	if (x == &bot) return y;
	if (y == &bot) return x;
	if (x == &top) return node_neg(y);
	if (y == &top) return node_neg(x);
	return new node("xor", {x, y});
}

void normalize_leq(node* n) {
	if (n->v.size() != 4)
		throw runtime_error("conditionals take exactly 4 arguments.");
	n->s = "eq";
	n->v[0] = node_and(n->v[0], node_neg(n->v[1]));
	n->v[1] = &bot;
}

void normalize_lt(node* n) {
	if (n->v.size() != 4)
		throw runtime_error("conditionals take exactly 4 arguments.");
	n->s = "eq";
	n->v[0] = node_and(n->v[0], node_neg(n->v[1]));
	n->v[1] = &bot;
	n->v[2] = new node("neq",
		{node_and(node_neg(n->v[0]), n->v[1]), &bot, n->v[2], n->v[3]});
}

void normalize(node* n) {
	if (!n) return;
	for (node* k : n->v) normalize(k);
	if (n->s == "leq") normalize_leq(n);
	else if (n->s == "geq") swap(n->v[0], n->v[1]), normalize_leq(n);
	else if (n->s == "lt") normalize_lt(n);
	else if (n->s == "gt") swap(n->v[0], n->v[1]), normalize_lt(n);
	else if (n->s == "eq" || n->s == "neq")
		n->v[0] = node_xor(n->v[0], n->v[1]), n->v[1] = &bot;
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
	if (n->s == "xor") {
		if (n->v.size() != 2)
			throw runtime_error("xor() takes exactly two arguments");
		return bdd_xor(get_bf(n->v[0]), get_bf(n->v[1]));
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
	cout << *n << endl << "normalized: " << endl;
	normalize(n);
	cout << *n << endl;
	out<char>(cout << "bdd: " << endl, get_bf(n)) << endl;
}
