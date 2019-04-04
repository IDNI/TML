#include "rule.h"
#include "driver.h"
#include <iostream>
#include <sstream>
using namespace std;

wostream& operator<<(wostream& os, const node& n) {
	return os<<n[0]<<' '<<n[1]<<' '<<n[2];
}

wostream& bdd_out(wostream& os,size_t n){
	return bdd_out(os<<L'['<<n<<L']',getnode(n));
}

wostream& bdd_out(wostream& os, const node& n) { //print bdd in ?: syntax
	return	nleaf(n) ? os << (ntrueleaf(n) ? L'T' : L'F') : (bdd_out(
		os<<n[0]<<L'?',getnode(n[1])),bdd_out(os<<L':',getnode(n[2])));
}

wostream& operator<<(wostream& os, const pair<cws, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

wostream& operator<<(wostream& os, const lexeme& l) {
	for (cws s = l[0]; s != l[1]; ++s) os << *s;
	return os;
}

wostream& operator<<(wostream& os, const bools& x) {
	for (auto y:x) os << (y?1:0);
	return os;
}

wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y:x) os << y << endl;
	return os;
}

wostream& operator<<(wostream& os, const term& t) {
	os << t.rel << ' ';
	for (auto x : t.args) os << x << ' ';
	return os;
}

wostream& operator<<(wostream& os, const matrix& m) {
	for (const term& t : m) os << t << ',';
	return os;
}

wostream& operator<<(wostream& os, const matrices& m) {
	for (const matrix& x : m) os << x << endl;
	return os;
}

template<typename F>
void driver::from_bits(size_t x, ints art, int_t rel, F f) const {
	allsat(x, bits * arlen(art), [art, rel, f, this](const bools& p) {
		const size_t ar = arlen(art);
		term v(false, rel, ints(ar, 0), art);
		for (size_t i = 0; i != ar; ++i)
			for (size_t b = 0; b != bits; ++b)
				if (p[POS(b, bits, i, ar)])
					v.args[i] |= 1 << b;
		f(v);
	});
}

matrix driver::from_bits(size_t x, ints art, int_t rel) const {
	const size_t ar = arlen(art);
	const vbools s = allsat(x, bits * ar);
	matrix r(s.size());
	for (term& v : r) v = term(false, rel, ints(ar, 0), art);
	size_t n = s.size(), i, b;
	while (n--)
		for (i = 0; i != ar; ++i)
			for (b = 0; b != bits; ++b)
				if (s[n][POS(b, bits, i, ar)])
					r[n].args[i] |= 1 << b;
	return r;
}

term driver::one_from_bits(size_t x, ints art, int_t rel) const {
	const size_t ar = arlen(art);
	bools s(bits * ar, true);
	if (!bdd_onesat(x, bits * ar, s)) return term();
	term r(false, rel, ints(ar), art);
	for (size_t i = 0; i != ar; ++i)
		for (size_t b = 0; b != bits; ++b)
			if (s[POS(b, bits, i, ar)])
				r.args[i] |= 1 << b;
	return r;
}

wostream& driver::printbdd(wostream& os, const matrices& t) const {
	for (auto m : t) printbdd(os, m) << endl;
	return os;
}

wostream& driver::print_term(wostream& os, const term& t) const {
	if (t.neg) os << L'~';
	os << dict.get_rel(t.rel) << L'(';
	for (size_t ar = 0, n = 0; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << L'(';
		for (int_t k = 0; k != t.arity[ar]; ++k) {
			if (t.args[n] < 0) throw 0;//os<<dict.get_var(t.args[n]);
			else if ((size_t)t.args[n] < dict.nsyms())
				os << dict.get_sym(t.args[n]);
			else os << L'[' << t.args[n] << L']';
			if (++n != t.args.size()) os << L' ';
		}
		++ar;
		while (ar<t.arity.size()&&t.arity[ar] == -2) ++ar, os<<L')';
	}
	return os << L')';
}

wostream& driver::printbdd(wostream& os, const matrix& t) const {
	set<wstring> s;
	for (auto v : t) {
		wstringstream ss;
		print_term(ss, v);
		s.emplace(ss.str());
	}
	for (auto& x : s) os << x << endl;
	return os;
}

#ifdef DEBUG
driver* drv;
wostream& printdb(wostream& os, lp *p) { return drv->printdb(os, p); }
wostream& printdiff(wostream& os, const diff_t& d) {
	return drv->printdiff(os, d);
}
wostream& printbdd(wostream& os, size_t t, ints ar, int_t rel) {
	//bdd_out(os<<allsat(t, arlen(ar)*drv->bits), t)<<endl;
	return drv->printbdd(os, t, ar, rel);
}
wostream& printbdd_one(wostream& os, size_t t, ints ar, int_t rel) {
	return drv->printbdd_one(os, t, ar, rel);
}
#endif

wostream& driver::printbdd(wostream& os, size_t t, ints ar, int_t rel) const {
	from_bits(t,ar,rel,[&os,this](const term&t){print_term(os, t)<<endl;});
	return os;
}

wostream& driver::printbdd_one(wostream& os, size_t t, ints ar, int_t rel)const{
	os << "one of " << bdd_count(t, bits * arlen(ar)) << " results: ";
	return print_term(os, one_from_bits(t, ar, rel));
}

wostream& driver::printdb(wostream& os, lp *p) const {
	return printdb(os, p->db);
}

wostream& driver::printdb(wostream& os, const db_t& db) const {
	for (auto x : db)
		if (builtin_rels.find(x.first.first) == builtin_rels.end()) {
			from_bits(*x.second, x.first.second,x.first.first, 
				[&os,this](const term&t){
				print_term(os, t)<<endl;});
		}
	return os;
}

wostream& driver::printdiff(wostream& os, const diff_t& d) const {
	for (auto x : d)
		if (builtin_rels.find(x.first.first) == builtin_rels.end())
			printbdd(os,from_bits(x.second,
				x.first.second,x.first.first));
	return os;
}

wostream& operator<<(wostream& os, const directive& d) {
	return os << L'@' << d.rel << L' ' << d.arg << L'.';
}

wostream& operator<<(wostream& os, const elem& e) {
	if (e.type == elem::CHR) return os << '\'' << *e.e[0] << '\'';
	if (e.type == elem::OPENP || e.type == elem::CLOSEP) return os<<*e.e[0];
	return e.type == elem::NUM ? os << e.num : (os << e.e);
}

wostream& operator<<(wostream& os, const production& p) {
	os << p.p[0] << L" -> ";
	for (size_t n = 1; n < p.p.size(); ++n) os << p.p[n] << L' ';
	return os << L'.';
}

wostream& operator<<(wostream& os, const raw_term& t) {
	if (t.neg) os << L'~';
	os << t.e[0];
	os << L'(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << L'(';
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];)
			if ((os << t.e[n++]), ++k != t.arity[ar]) os << L' ';
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar<t.arity.size()&&t.arity[ar] == -2) ++ar, os<<L')';
	}
	return os << L')';
}

wostream& operator<<(wostream& os, const raw_rule& r) {
	if (r.goal) os << L'!';
	if (r.pgoal) os << L'!';
	for (size_t n = 0; n < r.nheads(); ++n)
		if ((os << r.head(n)), n != r.nheads() - 1) os << L',';
	if (!r.nbodies()) return os << L'.';
	os << L" :- ";
	for (size_t n = 0; n < r.nbodies(); ++n)
		if ((os << r.body(n)), n != r.nbodies() - 1) os << L',';
	return os << L'.';
}

wostream& operator<<(wostream& os, const raw_prog& p) {
	for (auto x : p.d) os << x << endl;
	for (auto x : p.g) os << x << endl;
	for (auto x : p.r) os << x << endl;
	return os;
}

wostream& operator<<(wostream& os, const raw_progs& p) {
	if (p.p.size() == 1) os << p.p[0];
	else for (auto x : p.p) os << L'{' << endl << x << L'}' << endl;
	return os;
}
