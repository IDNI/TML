#include "tml.h"
#include "logprimes.h"
#define ever ;;

dlp& dlp::operator+=(clause *c) {
	if (!c->size()) return *this;
	c->sort();
	for (const clause *d : *this) if (*d == *c) return *this;
	for (size_t k = 0; k < c->size(); ++k)
		index[c->at(k)->rel()][size()] = k;
	push_back(c);
	return *this;
}

bool dlp::pe(clause &q, size_t dep) {
	typedef const pair<size_t, size_t> index_element;
	const clause *d;
	const literal *g;
	clause *t;
	env e;
	size_t iter = 0;
	uint64_t h = 0;
	static set<uint64_t> hs;
	for (ever) {
		++iter;
		for (size_t k = 0; k < q.size(); ++k) {
			g = q.at(k);
			//DEBUG(L"g: " << *g);
			for(index_element& x : index[-g->rel()]) {
				d = at(x.first);
				//DEBUG(L" d: " << *d << endl);
				if (!d->at(x.second)->unify(*g, e)) goto next;
				//DEBUG(L" unification passed with e: "<<e<<endl);
				if (!(t=new clause(*d, e))->add(*g))goto unsat;
				//DEBUG(L" t: " << *t << endl);
				if (t->size() == 1) {
					if (!q.add(*t->unit())) goto unsat;
				} else if (t->ground()) {
					bool s = false, f = false;
					for (size_t k = 0; k < t->size(); ++k){
						dlp &pp = *new dlp(*this);
						clause &qq = *new clause(q);
						size_t sz = qq.size();
						if (!qq.add(*t->at(k)) ||
							sz==qq.size()  ||
							hs.find(qq.rehash()) ==
							hs.end()) continue;
						f = true;
						hs.emplace(qq.hash),
						(s|=pp.pe(qq,1+dep));
					}
					if (!s) {
						if (!f) { *this+=t; goto next; }
						else goto unsat;
					}
				}
				else *this += t;
next:				e.clear();
				DEBUG(	endl<<L"finished iteration "<<iter
					<< " dep " << dep <<endl
					<< *this << endl << endl << q << endl);
			}
		}
		if (h == q.rehash() && q.size()) {
			wcout<<L"Done, satisfiable"<<endl;
			return true;
		} else if (hs.find(q.hash) != hs.end() || !q.size()) {
unsat:			wcout<<L"Done, unsatisfiable"<<endl;
			return false;
		} else hs.emplace(h = q.hash);
	}	
}

dlp::~dlp()  { for (const clause *c : *this) delete c; clear(); }

int32_t main() {
	setlocale(LC_ALL, "");
	dlp p;
	clause *q;
	p.program_read(wcin), q = clause::clause_read(wcin);
//	wcout<<p<<endl<<*q<<endl;
	p.pe(*q);
	wcout<<p<<endl<<*q<<endl;
}
