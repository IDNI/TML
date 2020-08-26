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
#include <set>
#include <cassert>
#include <cstdlib>
#include <iostream>
#include "bdd.h"
#include "query.test.h"

using namespace std;

wostream& bdd_out(wostream& os, const node& n);
wostream& bdd_out(wostream& os,size_t n);
wostream& operator<<(wostream& os, const struct tt& t);

wostream& operator<<(wostream& os, const ints& t) {
	for (auto x : t) os << x << ' ';
	return os;
}
wostream& operator<<(wostream& os, const vector<ints>& m) {
	for (const ints& t : m) os << t << endl;
	return os;
}

struct tt { // truth table
	size_t bits;
	set<bools> table;

	void addall(size_t var) {
		if (var == bits) return;
		set<bools> t = table;
		table.clear();
		for (auto x : t)
			x[var] = false, table.emplace(x),
			x[var] = true, table.emplace(x);
		addall(var+1);
	}

	tt() {}
	tt(size_t bits, bool full = false) : bits(bits) {
		if (full) {
			table.emplace(bools(bits, false));
			addall(0);
			assert(table.size() == (size_t)(1 << bits));
		}
	}

	void addrow(const bools& b) { table.emplace(b); }
	tt operator&(const tt& x) const {
		tt r(bits);
		for (auto& y : table)
			if (x.table.find(y) != x.table.end()) r.addrow(y);
		assert(r.bdd() == bdd_and(bdd(), x.bdd()));
		return r;
	}
	tt operator|(const tt& x) const {
		tt r(bits);
		r.table = table;
		for (auto& y : x.table) r.addrow(y);
		assert(r.bdd() == bdd_or(bdd(), x.bdd()));
		return r;
	}
	tt operator!() const {
		tt r(bits, true);
		for (auto& y : table) r.table.erase(y);
		assert(r.bdd() == bdd_and_not(T, bdd()));
		return r;
	}
	tt ex(size_t i) const {
		tt r = *this;
		for (bools x : table) x[i] = !x[i], r.addrow(x);
		bools b(bits, false);
		b[i] = true;
		assert(r.bdd() == bdd_ex(bdd(), b));
		return r;
	}
	tt ex(bools b) const {
		tt r = *this;
		for (size_t n = 0; n < bits; ++n) if (b[n]) r = r.ex(n);
		if (r.bdd() != bdd_ex(bdd(), b)) {
/*			COUT	<< "existential quantification of" <<endl
				<< *this << endl << "with" << endl << b
				<< endl << "wrongly returned" << endl
				<< allsat(bdd_ex(bdd(), b), bits) << endl
				<< "instead of" << endl << r << endl;*/
			assert(r.bdd() == bdd_ex(bdd(), b));
		}
		return r;
	}
	spnode bdd() const {
		spnode r = F;
		for (auto& x : table) {
			spnode y = T;
			for (size_t n = 0; n < bits; ++n)
				y = bdd_and(y, from_bit(n, x.at(n)));
			r = bdd_or(r, y);
		}
		vbools s = allsat(r, bits);
		set<bools> sb;
		for (auto& x : s) sb.emplace(x);
		if (sb != table) {
			COUT << "expected"<<endl;
			for (auto& x : table) COUT << x << endl;
			COUT << "got"<<endl<<allsat(r, bits);
			assert(sb == table);
		}
		return r;
	}
};

bools brnd(size_t bits) {
	bools r(bits);
	while (bits--) r[bits] = random() & 1;
	return r;
}

tt rndtt(size_t bits, size_t sz = 0) {
	tt r(bits);
	if (!sz) sz = random() % (1 << bits);
	while (sz--) r.addrow(brnd(bits));
	return r;
}

wostream& operator<<(wostream& os, const tt& t) {
	for (auto& x : t.table) os << x << endl;
	return os;
}

void test_and_many() {
	size_t bits = 3, tts = 3;
	for (size_t k = 0; k < 1500; ++k) {
		COUT<<k<<endl;
		tt *t = new tt[tts];
		for (size_t i = 0; i < tts; ++i) t[i] = rndtt(bits).ex(i);
		spnode r = T;
		for (size_t i = 0; i < tts; ++i) r = bdd_and(r, t[i].bdd());
		tt rr = t[0];
		for (size_t i = 1; i < tts; ++i) rr = rr & t[i];
		nodes v;
		for (size_t i = 0; i < tts; ++i) v.push_back(t[i].bdd());
		if (r != bdd_and_many(v)) {
			COUT<<endl;
			for (size_t i = 0; i < tts; ++i) COUT<<t[i]<<endl;
			COUT<<endl<<rr<<endl<<endl<<allsat(bdd_and_many(v),bits)
				<<endl<<endl<<allsat(r,bits)<<endl;
			assert(r == bdd_and_many(v));
		}
		assert(r == rr.bdd());
		if (r != F) COUT << "sat" << endl;
		delete[] t;
	}
}

void test_or_many() {
	size_t bits = 3, tts = 3;
	for (size_t k = 0; k < 1500; ++k) {
		COUT<<k<<endl;
		tt *t = new tt[tts];
		for (size_t i = 0; i < tts; ++i) t[i] = rndtt(bits).ex(i);
		spnode r = F;
		for (size_t i = 0; i < tts; ++i) r = bdd_or(r, t[i].bdd());
		tt rr = t[0];
		for (size_t i = 1; i < tts; ++i) rr = rr | t[i];
		nodes v;
		for (size_t i = 0; i < tts; ++i) v.push_back(t[i].bdd());
		if (r != bdd_or_many(v)) {
			COUT<<endl;
			for (size_t i = 0; i < tts; ++i) COUT<<t[i]<<endl;
			COUT<<endl<<rr<<endl<<endl<<allsat(bdd_or_many(v),bits)
				<<endl<<endl<<allsat(r,bits)<<endl;
			assert(r == bdd_or_many(v));
		}
		assert(r == rr.bdd());
		if (r != T) COUT << "tau" << endl;
		delete[] t;
	}
}

int main() {
	size_t bits = 10, args = 17;
	for (size_t n = 0; n != bits; ++n)
		for (size_t k = 0; k != args; ++k)
			assert(ARG(POS(n, bits, k, args), args) == k),
			assert(BIT(POS(n, bits, k, args), args, bits) == n);
	bdd_init();
	test_query();
	srand(time(0));
	test_and_many();
	test_or_many();
//	exit(0);
	tt xt(3);
	xt.addrow({false, true, true});
	xt.addrow({true, true, false});
	xt.ex({false, true, true});
	tt *t = new tt[5];
	for (size_t i = 0; i < 10; ++i)
		for (size_t k = 1; k < 10; ++k) {
			t[0] = rndtt(k);
			t[1] = rndtt(k);
			t[2] = t[0] & t[1];
			t[3] = t[0] | t[1];
			t[4] = !t[0];
			tt *e = new tt[k];
			e[0] = t[0].ex(0);
			for (size_t j = 1; j < k; ++j) e[j] = e[j-1].ex(j);
			assert(!t[0].table.size() 
				|| e[k-1].table.size() == (size_t)(1 << k));
			delete[] e;
			t[0].ex(brnd(k));
			t[1].ex(brnd(k));
			COUT<<k<<endl;
		}
	return 0;
}
