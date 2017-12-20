#include "tml.h"
#include "logprimes.h"
#define ever ;;

dlp& dlp::operator+=(clause *c) {
	c->sort();
	for (const clause *d : *this) if (*d == *c) return *this;
	for (size_t k = 0; k < c->size(); ++k)
		index[c->at(k)->rel()][size()] = k;
	push_back(c);
	return *this;
}

void dlp::pe(clause &q) {
	typedef const pair<size_t, size_t> index_element;
	const clause *d;
	clause *t;
	const literal *g;
	env e;
	size_t  iter = 0;
	uint64_t h = 0;
	set<uint64_t> hs;
	for (ever) {
		++iter;
		for (size_t k = 0; k < q.size(); ++k) {
			g = q.at(k);
			for(index_element& x : index[-g->rel()]) {
				d = at(x.first);
				if (!d->at(x.second)->unify(*g, e)) { e.clear(); continue; }
				t = new clause(*d, e);
				if ((*t += *g).size() == 1) q += *t->unit();
				else *this += t;
				e.clear();
			}
		}
		if (h == q.hash) {
			wcout<<L"Done, satisfiable"<<endl;
			return;
		} else if (hs.find(q.hash) != hs.end()) {
			wcout<<L"Done, unsatisfiable"<<endl;
			return;
		} else hs.emplace(h = q.hash);
		//DEBUG(L"finished iteration "<<iter<< L" program len " << szp << endl);
	}	
}

dlp::~dlp()  { for (const clause *c : *this) delete c; clear(); }

int32_t main() {
	setlocale(LC_ALL, "");
	dlp p;
	clause *q;
	p.program_read(wcin), q = clause::clause_read(wcin);
	wcout<<p<<endl<<*q<<endl;
	p.pe(*q);
	wcout<<p<<endl<<*q<<endl;
}
