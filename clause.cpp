#include "clause.h"
#include <algorithm>

clause::clause(const clause& c, env& e) {for(literal *l:c)*this+=literal(*l,e);} 

bool clause::operator==(const clause &l) const {
	size_t sz = size();
	if (sz != l.size()) return false;
	for (size_t n = 0; n < sz; ++n)
		if (*at(n) != *l[n])
			return false;
	return true;
}

clause& clause::operator+=(const literal &t) {
	for (size_t n = 0, s = size(); n != s; ++n)
		if (t.same_atom(*at(n))) {
			if (at(n)->rel() != t.rel()) erase(begin()+n), rehash();
			return *this;
		}
	literal *l = new literal(t);
	return (hash += l->hash * size()), push_back(l), *this;
}

uint64_t clause::rehash() {
	hash = 0;
	for (size_t n = 0; n < size(); ++n)
		hash += (*this)[n]->rehash();
	return hash;
}

void clause::sort() { std::sort(begin(), end()); rehash(); }
void clause::flip() { for (literal *l : *this) l->flip(); rehash(); }
void clause::clear() { base::clear(); }
size_t clause::size() const { return base::size(); }
int32_t clause::lastrel() const { return back()->rel(); }
const literal* clause::at(size_t k) const { return base::at(k); }
literal* clause::unit() const { return size() > 1 ? 0 : (*this)[0]; }
clause::~clause() { for (literal *l : *this) delete l; clear(); }
