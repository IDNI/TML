#include "literal.h"
#include <cstring>

int32_t evaluate(int32_t v, env &e) {
	if (v > 0) return v;
	env::const_iterator it = e.find(v);
	if (it == e.end()) return v;
	int32_t u;
	while ((it = e.find(u = it->second)) != e.end());
	return e[v] = u;
} 

literal::literal(const literal &l) : base(l), hash(l.hash) {}
literal::literal(const literal &l, env& e) {
//	DEBUG(endl<<L"evaluating "<<(*this)<<L" with "<<e<<L" giving ");
	push_back(l[0]);
	for (size_t i = 1; i < l.size(); ++i) push_back(evaluate(l[i], e));
	rehash();
//	DEBUG(r << endl);
} 

void literal::push_back(int32_t i){base::push_back(i), hash+=lphash(i)*size();}
void literal::flip() { *prel() = -*prel(), rehash(); }

uint64_t literal::rehash() {
	hash = 0;
	for (size_t n = 0, s = size(); n < s; ++n) hash += lphash(at(n))*(n+1);
	return hash;
}

bool literal::unify(const literal &g, env &e) const {
	//DEBUG(endl<<L"unifying "<<*this<<L" with "<<g<<L" given "<<e);
	size_t sz = size();
	if (g.size() != sz) return false;
	int v;
	for (size_t i = 1; i < sz; ++i) // assuming same rel
		if ((v = ::evaluate(at(i), e)) > 0 && v != g[i]) return false;
		else if (v < 0) e[v] = g[i]; 
	//DEBUG(L" output " << e << endl);
	return true;
} 

bool literal::same_atom(const literal &l) const {
	return	abs(at(0)) == abs(l[0]) &&
		size() == l.size() &&
		!memcmp(parg(), l.parg(), (size() - 1)*sizeof(int32_t));
}

bool literal::ground() const {
	for (size_t n = 1; n < size(); ++n) if (at(n) < 0) return false;
	return true;
}

bool literal::operator==(const literal &l) const{return ((base)*this)==(base)l;}
bool literal::operator!=(const literal& l) const { return !(l==*(this)); }
const int32_t* literal::prel() const { return &((*((base*)this))[0]); }
const int32_t* literal::parg() const { return &((*((base*)this))[1]); }
int32_t* literal::prel() { return &((*((base*)this))[0]); }
int32_t* literal::parg() { return &((*((base*)this))[1]); }
literal::literal() : base() {}
literal::literal(size_t sz) : base(sz) {}
void literal::clear() { base::clear(); }
int32_t literal::rel() const { return at(0); }
size_t literal::size() const { return base::size(); }
int32_t literal::at(size_t k) const { return base::at(k); }
