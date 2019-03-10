#include <set>
#include <cassert>
#include <cstdlib>
#include <iostream>
#include "bdd.h"

using namespace std;

wostream& out(wostream& os, const node& n) { //print bdd in ?: syntax
	return	nleaf(n) ? os << (ntrueleaf(n) ? L'T' : L'F') :
		(out(os<<n[0]<<L'?',getnode(n[1])),out(os<<L':',getnode(n[2])));
}
wostream& out(wostream& os,size_t n){return out(os<<L'['<<n<<L']',getnode(n));}
wostream& operator<<(wostream& os, const bools& x) {
	for (auto y:x) os << (y?1:0);
	return os;
}
wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y:x) { os << y << endl; } return os; }
wostream& operator<<(wostream& os, const struct tt& t);

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
			wcout	<< "existential quantification of" <<endl
				<< *this << endl << "with" << endl << b
				<< endl << "wrongly returned" << endl
				<< allsat(bdd_ex(bdd(), b), bits) << endl
				<< "instead of" << endl << r << endl;
			assert(r.bdd() == bdd_ex(bdd(), b));
		}
		return r;
	}
	size_t bdd() const {
		size_t r = F;
		for (auto& x : table) {
			size_t y = T;
			for (size_t n = 0; n < bits; ++n)
				y = bdd_and(y, from_bit(n, x.at(n)));
			r = bdd_or(r, y);
		}
		vbools s = allsat(r, bits);
		set<bools> sb;
		for (auto& x : s) sb.emplace(x);
		if (sb != table) {
			wcout << "expected"<<endl;
			for (auto& x : table) wcout << x << endl;
			wcout << "got"<<endl<<allsat(r, bits);
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

tt rndtt(size_t bits) {
	tt r(bits);
	size_t sz = random() % (1 << bits);
	while (sz--) r.addrow(brnd(bits));
	return r;
}

wostream& operator<<(wostream& os, const tt& t) {
	for (auto& x : t.table) os << x << endl;
	return os;
}

void test_add_many() {
	for (size_t k = 0; k < 50; ++k) {
		tt *t = new tt[5];
		for (size_t i = 0; i < 5; ++i) t[i] = rndtt(8).ex(i);
		size_t r = T;
		for (size_t i = 0; i < 5; ++i) r = bdd_and(r, t[i].bdd());
		if (!leaf(r)) {
			vector<size_t> v;
			for (size_t i = 0; i < 5; ++i) v.push_back(t[i].bdd());
			assert(r == bdd_and_many(v, 0, v.size()));
		}
		delete[] t;
	}
}

int main() {
	bdd_init();
	srand(time(0));
	test_add_many();
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
			wcout<<k<<endl;
		}
	return 0;
}
