#include "table.h"

bool cmpterm::operator()(term x, term y) const {
	return *x == *y ? memcmp(x, y, sizeof(int_t)**x)<0 : (*x < *y);
}

table::table(size_t ubits, size_t rbits, size_t arbits, dnf&& d, const term q, const table* t) :
	dnf(move(d)), ubits(ubits), rbits(rbits), arbits(arbits), q(q), t(t), sel(q) {}

table::table(size_t ubits, size_t rbits, size_t arbits, const term q, const table* t) :
	ubits(ubits), rbits(rbits), arbits(arbits), q(q), t(t), sel(q) {}

void table::get(const clause& c, size_t len, size_t rel, terms& r) const {
	size_t z = 0, k = 0, n, from = arbits + rbits, to = from + (len<<3), i;
	char *p = (char*)__builtin_alloca(to-from);
	int_t *t;
	for (n = from; n < to; ++n)
		if (c.has(n+1)) p[k++] = 1;
		else if (c.has(-n-1)) p[k++] = -1;
		else ++z, p[k++] = 0;
	if (z > 63)
		wcout<<L"Got more than 2^64-1=18446744073709551615 results (~2^"
			<< z << L" results)"<<endl, exit(0);
	for (i = 0; i < (size_t)(1 << z); ++i) {
		for (	*(t = new int_t[len]) = len, t[1] = rel,
			memset(t+2, 0, sizeof(int_t) * (len - 2)),
			n = from, k = 0; n < to; ++n)
			if (p[n-from] == -1 || (!p[n-from] && !getbit(i, k++))) continue;
			else setbit(t[2 + (n - from) / ubits], (n - from) % ubits);
		if (!r.emplace(t).second) delete[] t;
	}
}

void table::get(const clause& c, terms& r) const {
	size_t psz = 0, nsz = 0, n, z, k, len, rel, _z, _k, prel, nrel;
	for (n = 0; n < arbits; ++n)
		if (c.has(n+1)) setbit(psz, n);
		else if (c.has(-n-1)) setbit(nsz, n);
	const size_t m = (~(psz | nsz)) & ((1 << arbits)-1);
	for ((z = 1 << __builtin_popcount(m)), k=len=0; z--; k=len=0) {
		for (n = 0; n < arbits; ++n)
			if (psz & (1 << n)) setbit(len,n);
			else if (nsz & (1 << n)) continue;
			else setbit(len, getbit(z, k++));
		for (prel = nrel = 0; n < rbits + arbits; ++n)
			if (c.has(n+1)) setbit(prel,n-arbits);
			else if (c.has(-n-1)) setbit(nrel,n-arbits);
		const size_t _m = (~(prel | nrel)) & ((1 << rbits)-1);
		for (_z=1<<__builtin_popcount(_m), _k=0, rel=0; _z--; _k=rel=0)
			for (n = 0; n < rbits; get(c, len, rel, r), ++n)
				if (prel & (1 << n)) setbit(rel, n);
				else if (nrel & (1 << n)) continue;
				else setbit(rel, getbit(_z, _k++));
	}
}

void table::add(term t) {
	clause c;
	size_t v = 0;
	for (size_t n = 0; n < arbits; ++n)
		c.add(*t & (1 << n) ? -++v : ++v);
	for (size_t n = 0; n < rbits; ++n)
		c.add(t[1] & (1 << n) ? -++v : ++v);
	for (size_t k = 2; k < (size_t)*t; ++k)
		for (size_t n = 0; n < ubits; ++n)
			c.add(t[k] & (1 << n) ? -++v : ++v);
	dnf::add(move(c));
}

void table::get(terms& r) const {
	for (const clause& c : *this) get(c, r);
}

table table::select(term q) const {
	set<array<int_t, 3>> e;
	set<int_t> s;
	for (int_t n = 0, k; n < *q; ++n)
		if (q[n+2] < 0)
			for (k = 0; k < (int_t)ubits; ++k)
				s.emplace(getbit(q[n+2], k) ? k+1 : (-k-1));
		else if (n) for (k = n-1; k; --k)
			if (q[k+2] == q[n+2]) e.emplace(array<int_t,3>{n, (int_t)ubits, k});
	return table(ubits, rbits, arbits, eq(e, s), q, this);
}

table table::join(const table& db, const map<term, set<terms>>& p) {
	for (auto& def : p) {
		term h = def.first;
		for (const terms& alt: def.second)
			for (term b : alt) {
				table sel = db.select(b);
			}
	}
}
