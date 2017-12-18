#include "tml.h"
#include <algorithm>

int32_t evaluate(int32_t v, env &e) {
	if (v > 0) return v;
	env::const_iterator it = e.find(v);
	if (it == e.end()) return v;
	int32_t u;
	while ((it = e.find(u = it->second)) != e.end());
	return e[v] = u;
} 

literal::literal(const literal &l, env& e) {
//	DEBUG(endl<<L"evaluating "<<(*this)<<L" with "<<e<<L" giving ");
//	resize(l.size()), 
	push_back(l[0]);
	for (size_t i = 1; i < l.size(); ++i) push_back(evaluate(l[i], e));
//	DEBUG(r << endl);
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

bool literal::operator==(const literal &l) const{return ((base)*this)==(base)l;}
////////////////////////////////////////////////////////////////////////////////
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
			if (at(n)->rel() != t.rel()) erase(begin() + n);
			return *this;
		}
	push_back(new literal(t));
	return *this;
}
////////////////////////////////////////////////////////////////////////////////
dlp& dlp::operator+=(clause *c) {
	sort(c->begin(), c->end());
	for (const clause *d : *this) if (*d == *c) return *this;
	for (size_t k = 0; k < c->size(); ++k)
		index[c->at(k)->rel()][size()] = k;
	push_back(c);
	return *this;
}

void dlp::pe(dlp &q) {
	typedef const pair<size_t, size_t> index_element;
	const clause *d;
	const literal *g;
	size_t  szp, szq, iter = 0;
	do {	++iter, szp = size(), szq = q.size();
		for (size_t n = 0; n < q.size(); ++n)
			for (size_t k = 0; k < q[n]->size(); ++k) {
				g = q.at(n)->at(k);
				for(index_element& x : index[-g->rel()])
					d = at(x.first),
					pe(d, d->at(x.second), g, q);
			//DEBUG(L"finished iteration "<<iter<< L" program len " << szp << endl);
	}	
	} while (size() != szp || q.size() != szq);
}

void dlp::pe(const clause *c, const literal *l, const literal *g, dlp &q) {
	env e;
	clause *d;
//	DEBUG(L"pe: c="<<*c<<L" l="<<*l<<L" g="<<*g<<endl);
	if (l->unify(*g, e)) {
		d = new clause(*c, e);
		if ((*d += *g).size() == 1) q += d;
		else *this += d;
	}
}

dlp::~dlp()  { for (const clause *c : *this) delete c; clear(); }
clause::~clause() { for (literal *l : *this) delete l; clear(); }

int32_t main() {
	setlocale(LC_ALL, "");
	dlp p, q;
	p.program_read(wcin), q.program_read(wcin);
	p.pe(q);
	wcout<<p<<endl<<q<<endl;
}
