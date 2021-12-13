#include "earley.h"

using namespace std;

ostream& operator<<(ostream& os, const vector<string>& v) {
	for (auto &s : v) if (s.size()) os << s << ' '; else os << "ε ";
	return os;
}

#ifdef DEBUG
ostream& operator<<(ostream& os, const earley::lit& l) {
	if (l.nt()) return os << l.n();
	else return os << (l.c() == '\0' ? 'e' : l.c());
}

ostream& operator<<(ostream& os, const vector<earley::lit>& v) {
	for (auto &l : v) os << l << ' ';
	return os;
}
#endif

bool earley::all_nulls(const vector<lit>& p) const {
	for (size_t k = 1; k != p.size(); ++k)
		if ((!p[k].nt() && p[k].c() != '\0') || (p[k].nt() &&
			nullables.find(p[k].n()) == nullables.end()))
			return false;
	return true;
}

earley::earley(const vector<pair<string, vector<vector<string>>>>& g) {
	set<string> nt;
	for (const auto &x : g) nt.insert(x.first);
	for (const auto &x : g)
		for (auto &y : x.second) {
			G.push_back({lit(d.get(x.first))});
			for (auto &s : y)
				if (nt.find(s) != nt.end())
					G.back().emplace_back(d.get(s));
				else if (s.size() == 0)
					G.back().emplace_back('\0');
				else for (char_t c : s)
					G.back().emplace_back(c);

	}
	start = lit(d.get("S"));
	for (size_t n = 0; n != G.size(); ++n) nts[G[n][0]].insert(n);
	size_t k;
	do {
		k = nullables.size();
		for (const auto& p : G)
			if (all_nulls(p))
				nullables.insert(p[0].n());
	} while (k != nullables.size());
#ifdef DEBUG
	for (auto x : g)
		for (auto y : x.second)
			cout << x.first << '=' << y << endl;
	for (auto x : G) cout << x << endl;
	for (auto x : d.m) cout << x.first << ' '<< x.second << endl;
#endif
}

ostream& earley::print(ostream& os, const item& i) const {
	os << i.set << ' ' << i.from << ' ';
	for (size_t n = 0; n != G[i.prod].size(); ++n) {
		if (n == i.dot) os << "* ";
		if (G[i.prod][n].nt()) os << d.get(G[i.prod][n].n()) << ' ';
		else if (G[i.prod][n].c() == '\0') os << "ε " << ' ';
		else os << G[i.prod][n].c() << ' ';
	}
	if (G[i.prod].size() == i.dot) os << '*';
	return os;
}

set<earley::item>::iterator earley::add(set<item>& t, const item& i) {
	DBG(print(cout << "adding ", i) << endl;)
	set<item>::iterator it = S.find(i);
	if (it != S.end()) return it;
	if ((it = t.find(i)) != t.end()) return it;
	it = t.insert(i).first;
	if (nullable(*it))
		add(t, item(it->set, it->prod, it->from, it->dot + 1))->
			advancers.insert(i);
	return it;
}

void earley::complete(const item& i, set<item>& t) {
	DBG(print(cout << "completing ", i) << endl;)
	for (	auto it = S.lower_bound(item(i.from, 0, 0, 0));
		it != S.end() && it->set == i.from; ++it)
		if (	G[it->prod].size() > it->dot &&
			get_lit(*it) == get_nt(i))
			add(t, item(i.set, it->prod, it->from, it->dot + 1))->
				completers.insert(i);
}

void earley::predict(const item& i, set<item>& t) {
	DBG(print(cout << "predicting ", i) << endl;)
	for (size_t p : nts[get_lit(i)]) {
		item j(i.set, p, i.set, 1);
		add(t, j)->advancers.insert(i);
		DBG(print(cout << "predicting added ", j) << endl;)
	}
}

void earley::scan(const item& i, size_t n, char ch) {
	if (ch != get_lit(i).c()) return;
	item j(n + 1, i.prod, i.from, i.dot + 1);
	S.insert(j).first->advancers.insert(i);
	DBG(print(cout, i) << ' ';)
	DBG(print(cout << "scanned " << ch << " and added ", j) << endl;)
}

bool earley::recognize(const char_t* s) {
	cout << "recognizing: " << s << endl;
	size_t len = strlen(s);
	S.clear();//, S.resize(len + 1);//, C.clear(), C.resize(len + 1);
	for (size_t n : nts[start]) S.emplace(0, n, 0, 1);
	set<item> t;
	for (size_t n = 0; n != len + 1; ++n) {
		DBG(cout << "pos " << n << endl;)
		do {
			S.insert(t.begin(), t.end());
			t.clear();
			for (	auto it = S.lower_bound(item(n, 0, 0, 0));
				it != S.end() && it->set == n; ++it) {
				DBG(print(cout << "processing ", *it) << endl;)
				if (completed(*it)) complete(*it, t);
				else if (get_lit(*it).nt()) predict(*it, t);
				else if (n < len) scan(*it, n, s[n]);
			}
		} while (!t.empty());
		for (auto i : S) {
			if(!completed(i)) continue;
			print(cout, i);
			for( auto &a : i.advancers)
				cout<< " adv by ", print(cout, a);
			for( auto &c : i.completers)
				cout<< " cmplete by ", print(cout, c);
			cout<<endl;
		}
/*		cout << "set: " << n << endl;
		for (	auto it = S.lower_bound(item(n, 0, 0, 0));
			it != S.end() && it->set == n; ++it)
			print(*it);*/
	}
	for (const item& i : S) if (completed(i)) citem.emplace(i);
	pfgraph.clear();
	bool found = false;

	for (size_t n : nts[start])
		if (S.find( item(len, n, 0, G[n].size())) != S.end()) {
			found = true;
		}
	lit root = start;
	root.st = 0 ;
	root.en = len;
	forest(root);
	to_dot();
	return found;
}
/*
void earley::forest(ast& a, const vector<ast>& v) const {
	size_t from = a.i.from;
	for (size_t a.i.dot = 1; a.i.dot != G[a.i.prod].size(); ++a.i.dot)
		if (!get_lit(a.i).nt()) ++from;
		else {
			;
		}
}

void earley::forest(size_t prod, size_t from, const vector<ast>& v,
		function<void(ast&)> f) const {
}

vector<ast> earley::forest() {
	vector<ast> v;
	for (const item& i : S) if (completed(i)) v.emplace_back(i);
	S.clear();
	for (size_t n : nts.at(start))
		for (ast& a : v)
			if (a.i == item(len, n, 0, G[n].size()))
				forest(a, v);
	return v;
}
*/

const std::vector<earley::item> earley::find_all( size_t xfrom, size_t nt, int end ) {
	std::vector<item> ret;
	
	for(auto it = citem.begin(); it != citem.end(); it++) {
		if( it->from == xfrom && nts[nt].count(it->prod) ){
			if( end != -1 && (int)it->set == end ) ret.push_back(*it);
			else if( end == -1) ret.push_back(*it);
		}
	}	
	return ret;
}
bool earley::to_dot() {
	
	std::stringstream ss;
	auto keyfun = [this] (const nidx_t & k){
		stringstream l;
		k.nt()?l <<d.get( k.n()): k.c() =='\0' ? l<<"ε" : l<<k.c();
		l <<"_"<<k.st<<"_"<<k.en<<"_";
		return l.str();
	};
	ss << endl<< "node" << "[ ordering =\"out\"];";
	ss << endl<< "graph" << "[ overlap =false, splines = true];";
	for( auto &it: pfgraph ) {
		string key = keyfun(it.first);
		ss << endl<< key << "[label=\""<< key <<"\"];";
		size_t p=0;
		stringstream pstr;
		for( auto &pack : it.second) {
			pstr<<key<<p++;
			ss << std::endl<<pstr.str() << "[shape = point,label=\""<< pstr.str() << "\"];";
			ss << std::endl << key   <<"->" << pstr.str()<<';';
			for( auto & nn: pack) {
				string nkey = keyfun(nn);
				ss  << endl<< nkey << "[label=\""<< nkey<< "\"];",
				ss << std::endl << pstr.str()   <<"->" << nkey<< ';';
			}
			pstr.str("");
		}
	}

	static size_t c = 0;
	stringstream ssf;
	ssf<<"graph"<<c++ << ".dot";
	std::ofstream file(ssf.str());
	file << "digraph {" << endl<< ss.str() << endl<<"}"<<endl;
	file.close();
	return true;

}

void earley::sbl_chd_forest( const item &eitem, std::vector<nidx_t> curchd, size_t xfrom, std::set<std::vector<nidx_t>> &ambset  ) {

//	for(size_t len = 1, xfrom = curchd.from ; len < G[curchd.prod].size(); len++ ) {

	if( G[eitem.prod].size() <= curchd.size()+1 )  {
		if(curchd.back().en == eitem.set)
			 ambset.insert(curchd);
		return;
	}
	lit nxtl = G[eitem.prod ][curchd.size()+1];  // curchd.size() refers to index of cur literal to process in the rhs of production
	if(!nxtl.nt())  nxtl.st = xfrom, nxtl.en = nxtl.c() !='\0' ? ++xfrom: xfrom,
		curchd.push_back(nxtl), sbl_chd_forest(eitem, curchd, xfrom, ambset);
	else {
		//forest(v);
		nxtl.st = xfrom;
		auto &nxtl_froms = find_all(xfrom, nxtl.n());
		for( auto &v: nxtl_froms  ) {
			if( v.set > eitem.set) continue;		
			nxtl.en = v.set, curchd.push_back(nxtl), xfrom = v.set,
			sbl_chd_forest(eitem, curchd, xfrom, ambset);
			curchd.pop_back();
		}
	}
}

bool earley::forest ( lit &root ) {
	
	if(!root.nt()) return false;
	if(pfgraph.find(root) != pfgraph.end()) return false;

	auto nxtset = find_all(root.st, root.n(), root.en);
	std::set<std::vector<nidx_t>> ambset;
	for(const item &cur: nxtset) {
		lit cnode  = G[cur.prod][0];
		cnode.st = cur.from;
		cnode.en = cur.set;	
		vector<nidx_t> nxtlits;
		sbl_chd_forest(cur, nxtlits, cur.from, ambset );
		pfgraph[cnode] = ambset;
		for ( auto aset: ambset )
			for( lit& nxt: aset) {
				forest( nxt);
			}
	}	
	return true;
}


int main() {
	// S = eps | aSbS
	earley e({
			{"S", { { "b" }, { "S", "S" } } }
			//{"S", { { "" }, { "a", "S", "b", "S" } } },
//			{"S", { { "" }, { "A", "S", "B", "S" } } },
//			{"A", { { "" }, { "A", "a" } } },
//			{"B", { { "b" }, { "B", "b" } } }
		});
	cout << e.recognize("bbb") << endl << endl;
	
	earley e1({{"S", { { "b" }, {"S"} }}});
	cout << e1.recognize("b") << endl << endl;

	earley e2({ {"S", { { "a", "X", "X", "c" }, {"S"} }},
				{"X", { {"X", "b"}, { "" } } },

	});
	cout << e2.recognize("abbc") << endl << endl;

/*	cout << e.recognize("aa") << endl << endl;
	cout << e.recognize("aab") << endl << endl;
	cout << e.recognize("abb") << endl << endl;
	cout << e.recognize("aabb") << endl << endl;
	cout << e.recognize("aabbc") << endl << endl;
*/
	return 0;
}
