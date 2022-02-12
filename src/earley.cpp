#include "earley.h"
#include <utility>
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

earley::earley(const vector<production> &g) {
	set<string> nt;
	for (const auto &x : g) nt.insert(x.p[0].to_str());
	for (const auto &x : g) {
		G.emplace_back();
		for (auto &y : x.p) {
			if (nt.find(y.to_str()) != nt.end())
				G.back().emplace_back(d.get(y.to_str()));
			else if (x.p.size() == 2 && y.to_str() =="null" )
				G.back().emplace_back('\0');
			else for (char c : y.to_str())
				G.back().emplace_back(c);
		}
	}
	start = lit(d.get("start"));
	for (size_t n = 0; n != G.size(); ++n) nts[G[n][0]].insert(n);
	size_t k;
	do {
		k = nullables.size();
		for (const auto& p : G)
			if (all_nulls(p))
				nullables.insert(p[0].n());
	} while (k != nullables.size());
#ifdef DEBUG
	for (auto x : G) o::dbg() << x << endl;
	for (auto x : d.m) o::dbg() << x.first << ' '<< x.second << endl;
#endif
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
				else for (char c : s)
					G.back().emplace_back(c);

	}
	start = lit(d.get("start"));
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
			o::dbg() << x.first << '=' << y << endl;
	for (auto x : G) o::dbg() << x << endl;
	for (auto x : d.m) o::dbg() << x.first << ' '<< x.second << endl;
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
	DBG(print(o::dbg() << "adding ", i) << endl;)
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
	DBG(print(o::dbg() << "completing ", i) << endl;)
	for (	auto it = S.lower_bound(item(i.from, 0, 0, 0));
		it != S.end() && it->set == i.from; ++it)
		if (	G[it->prod].size() > it->dot &&
			get_lit(*it) == get_nt(i))
			add(t, item(i.set, it->prod, it->from, it->dot + 1))->
				completers.insert(i);
}

void earley::predict(const item& i, set<item>& t) {
	DBG(print(o::dbg() << "predicting ", i) << endl;)
	for (size_t p : nts[get_lit(i)]) {
		item j(i.set, p, i.set, 1);
		add(t, j)->advancers.insert(i);
		DBG(print(o::dbg() << "predicting added ", j) << endl;)
	}
}

void earley::scan(const item& i, size_t n, char ch) {
	if (ch != get_lit(i).c()) return;
	item j(n + 1, i.prod, i.from, i.dot + 1);
	S.insert(j).first->advancers.insert(i);
	DBG(print(o::dbg(), i) << ' ';)
	DBG(print(o::dbg() << "scanned " << ch << " and added ", j) << endl;)
	/*
	stringstream ss;
	ss<<" encountered '"<<ch <<"' at position "<< n <<", try '"<<get_lit(i).c() << "' instead";
	parse_error( 0, ss.str().c_str() );	
	*/
}

bool earley::recognize(const char* s) {
	DBG(o::dbg() << "recognizing: " << s << endl;)
	inputstr = s;
	size_t len = strlen(s);
	S.clear();//, S.resize(len + 1);//, C.clear(), C.resize(len + 1);
	for (size_t n : nts[start]) S.emplace(0, n, 0, 1);
	set<item> t;
	for (size_t n = 0; n != len + 1; ++n) {
		DBG(o::dbg() << "pos " << n << endl;)
		do {
			S.insert(t.begin(), t.end());
			t.clear();
			for (	auto it = S.lower_bound(item(n, 0, 0, 0));
				it != S.end() && it->set == n; ++it) {
				DBG(print(o::dbg() << "processing ", *it) << endl;)
				if (completed(*it)) complete(*it, t);
				else if (get_lit(*it).nt()) predict(*it, t);
				else if (n < len) scan(*it, n, s[n]);
			}
		} while (!t.empty());
/*
#ifdef DEBUG
		for (auto i : S) {
			if(!completed(i)) continue;
			DBG(print(o::dbg(), i);)
			for( auto &a : i.advancers)
				{ DBG(o::dbg()<< " adv by ") ; DBG(print(o::dbg(), a)); }
			for( auto &c : i.completers)
				{ DBG(o::dbg()<< " cmplete by ") ; DBG(print(o::dbg(), c)); }
			DBG(o::dbg()<<endl;)
#endif
*/
/*		DBG(o::dbg() << "set: " << n << endl;)
		for (	auto it = S.lower_bound(item(n, 0, 0, 0));
			it != S.end() && it->set == n; ++it)
			print(*it);*/
	}
	bool found = false;
	for (size_t n : nts[start])
		if (S.find( item(len, n, 0, G[n].size())) != S.end()) {
			found = true;
		}
	nidx_t root(start, {0,len});
	pfgraph.clear();	
	emeasure_time_start( ts0, te0 );
	for (const item& i : S) 
		if (completed(i)) //citem.emplace(i);
			sorted_citem[G[i.prod][0].n()][i.from].emplace_back(i);
	emeasure_time_start( ts1, te1 );
	forest(root);
	(emeasure_time_end( ts1, te1 ), o::inf()<<"\n");
	(emeasure_time_end( ts0, te0 ), o::inf()<<" :: forest time "<<endl) ;
	to_dot();
	to_tml_facts();
	to_tml_rule();
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
	if(end == -1)
		return sorted_citem[nt][xfrom];
	else {
		auto v = sorted_citem[nt][xfrom];
		for(  auto &it :v )
			if( (int)it.set == end ) ret.push_back(it);
		return ret;
	}	
	/*
	for(auto it = citem.begin(); it != citem.end(); it++) {
		if( it->from == xfrom && nts[nt].count(it->prod) ){
			if( end != -1 && (int)it->set == end ) ret.push_back(*it);
			else if( end == -1) ret.push_back(*it);
		}
	}	
	return ret;
	*/
}
std::string earley::grammar_text(){
	stringstream txt;
	for (const auto &p : G) {
		txt << ("\n\\l");
		size_t i=0;
		for( const auto &l : p){
			if(l.nt()) txt << d.get(l.n());
			else if ( l.c() != '\0') txt << l.c();
			else txt << "ε";
			txt<< " ";
			if( i++ == 0) txt <<"-> ";
		}
	}		
	return txt.str();
}
bool earley::to_tml_facts() const { 
	stringstream ss;
	auto str_rel_output = [&ss] ( string rel, size_t id, vector<variant<size_t, string>> args){
	ss << rel << "("<< id;
	for(auto &a : args) 
		if( std::holds_alternative<size_t>(a)) ss << " "<< std::get<size_t>(a);
		else ss <<" "<<std::get<string>(a);
	ss << ")."<<std::endl;
	};

	visit_forest(str_rel_output);

	static size_t c = 0;
	stringstream ssf;
	ssf<<"parse_graph"<<c++ << ".tml";
	std::ofstream file(ssf.str());
	file << ss.str();
	file.close();
	return true;

}
template<typename T>
bool earley::visit_forest(T out_rel) const {
//bool earley::visit_forest(std::function<void(std::string,size_t, std::vector<std::variant<size_t, std::string>>)> out_rel) const{
	std::stringstream ss;
	auto get_args = [this] (const nidx_t & k ){
		arg_t args;
		if (k.nt()) args.emplace_back("\"" + d.get(k.n()) + "\"");
		else if (k.c() == '\0' )  args.emplace_back("ε");
		else args.emplace_back(string({'"', k.c(), '"'}));
		args.emplace_back(k.span.first);
		args.emplace_back(k.span.second);
		return args;
	};

	map<nidx_t, size_t> nid;
	size_t id = 0;
	for( auto &it: pfgraph ){
		nid[it.first] = id;
		// skip ids for one child ambig node
		id += it.second.size()==1? 0:it.second.size(); // ambig node ids;
		DBG(assert(it.second.size()!= 0));
		id++;
	}
	ss<<std::endl;
	for( auto &it: pfgraph ) {
		arg_t ndesc = get_args(it.first);
		out_rel("node", nid[it.first], ndesc);
		size_t p = 0;
		for( auto &pack : it.second) {
			if(it.second.size() > 1) {  //skipping if only one ambigous node, an optimization
				++p;
				out_rel("edge", nid[it.first], { nid[it.first] + p } );
				out_rel("node", nid[it.first] + p, {} );
			}
			for( auto & nn: pack) {
				if(nid.find(nn) == nid.end()) nid[nn] = id++; // for terminals, not seen before
				arg_t nndesc = get_args(nn);
				out_rel("node", nid[nn], nndesc );
				out_rel("edge", nid[it.first] + p, {nid[nn]} );
			}
		}
	}
	return true;
}
vector<earley::arg_t> earley::get_parse_graph_facts(){
	vector<arg_t> rts;
	auto rt_rel_output = [&rts] ( string rel, size_t id, vector<variant<size_t, string>> args){
		args.insert(args.begin(), {rel, id });
		rts.emplace_back(args);
	};
	visit_forest(rt_rel_output);
	return rts;
}
string earley::to_tml_rule(const nidx_t nd) const {
	
	std::stringstream ss;
	if(nd.l.nt())	ss << d.get( nd.l.n());
	else if( nd.l.c() =='\0' ) ss <<"ε";
	else  ss << nd.l.c();

	ss <<"(" <<nd.span.first<< " "<< nd.span.second <<")";
	return ss.str();
}
bool earley::to_tml_rule() const{
	stringstream ss;
	set<string> terminals;

	for( auto &it: pfgraph ) {
		for( auto &pack : it.second) { 
			ss <<to_tml_rule(it.first)<< ":-";
			for( size_t i=0; i< pack.size(); i++) {
				// if terminal
				if(pfgraph.find(pack[i]) == pfgraph.end()) terminals.insert(to_tml_rule(pack[i]));
				ss << to_tml_rule(pack[i]) << (i == pack.size()-1 ? ".":",");
			};
			ss << std::endl;
		}
	}

	for( auto &t: terminals)
		ss << t <<"." << std::endl;

	static size_t c = 0;
	stringstream ssf;
	ssf<<"parse_rules"<<c++ << ".tml";
	std::ofstream file(ssf.str());
	file << ss.str();
	file.close();
	return true;

}
bool earley::to_dot() {
	
	std::stringstream ss;
	auto keyfun = [this] (const nidx_t & k){
		stringstream l;
		k.nt()?l <<d.get( k.n()): k.c() =='\0' ? l<<"ε" : l<<k.c();
		l <<"_"<<k.span.first<<"_"<<k.span.second<<"_";
		string desc = l.str();
		
		return std::pair<size_t, string>(std::hash<string>()(desc), desc);
	};
	ss << "_input_"<<"[label =\""<<inputstr <<"\", shape = rectangle]" ;
	ss << "_grammar_"<<"[label =\""<<grammar_text() <<"\", shape = rectangle]" ;
	ss << endl<< "node" << "[ ordering =\"out\"];";
	ss << endl<< "graph" << "[ overlap =false, splines = true];";
	static set<pair<size_t, size_t>> edgedone;
	edgedone.clear();
	for( auto &it: pfgraph ) {
		auto key = keyfun(it.first);
		ss << endl<< key.first << "[label=\""<< key.second <<"\"];";
		size_t p=0;
		stringstream pstr;
		for( auto &pack : it.second) {
			pstr<<key.second<<p++;
			auto ambkey = std::hash<string>()(pstr.str());
			ss << std::endl<<ambkey << "[shape = point,label=\""<< pstr.str() << "\"];";
			if(edgedone.insert({key.first, ambkey}).second )
				ss << std::endl << key.first   <<"->" << ambkey<<';';
			for( auto & nn: pack) {
				auto nkey = keyfun(nn);
				ss  << endl<< nkey.first << "[label=\""<< nkey.second<< "\"];";
				if(edgedone.insert({ambkey, nkey.first}).second )
					ss << std::endl << ambkey   <<"->" << nkey.first<< ';';
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
// collects all possible variations of the given item's rhs while respecting the span of the item
// and stores them in the set ambset. 
void earley::sbl_chd_forest( const item &eitem, std::vector<nidx_t> &curchd, size_t xfrom, std::set<std::vector<nidx_t>> &ambset  ) {

	//check if we have reached the end of the rhs of prod
	if( G[eitem.prod].size() <= curchd.size()+1 )  {
		// match the end of the span we are searching in.
		if(curchd.back().span.second == eitem.set) 		
			 ambset.insert(curchd);
		return;
	}
	// curchd.size() refers to index of cur literal to process in the rhs of production
	nidx_t nxtl = G[eitem.prod ][curchd.size()+1];
	// set the span start/end of the terminal symbol 
	if(!nxtl.nt()) {
		nxtl.span.first = xfrom;
		// for empty, use same span edge as from
		if( nxtl.c() == '\0') nxtl.span.second = xfrom;
		// ensure well-formed combination (matching input) early
		else if (xfrom < inputstr.size() && inputstr.at(xfrom) == nxtl.c())  
			nxtl.span.second = ++xfrom ;
		else // if not building the correction variation, prune this path quickly 
			return ;
		// build from the next in the line
		size_t lastpos = curchd.size();
		curchd.push_back(nxtl), sbl_chd_forest(eitem, curchd, xfrom, ambset);
		curchd.erase(curchd.begin() + lastpos, curchd.end());
	}
	else {
		// get the from/to span of all non-terminals in the rhs of production.
		nxtl.span.first = xfrom;
		//auto &nxtl_froms = find_all(xfrom, nxtl.n());
		auto &nxtl_froms = sorted_citem[nxtl.n()][xfrom];
		for( auto &v: nxtl_froms  ) {
			// ignore beyond the span
			if( v.set > eitem.set) continue;
			// store current and recursively build for next nt
			size_t lastpos = curchd.size(); 
			nxtl.span.second = v.set, curchd.push_back(nxtl), xfrom = v.set,
			sbl_chd_forest(eitem, curchd, xfrom, ambset);
			curchd.erase(curchd.begin() + lastpos, curchd.end());
		}
	}
}

// builds the forest starting with root
bool earley::forest ( const nidx_t &root ) {
	if(!root.nt()) return false;
	if(pfgraph.find(root) != pfgraph.end()) return false;

	//auto nxtset = find_all(root.span.first, root.n(), root.span.second);
	auto &nxtset = sorted_citem[root.n()][root.span.first];
	std::set<std::vector<nidx_t>> ambset;
	for(const item &cur: nxtset) {
		if(cur.set != root.span.second) continue;
		nidx_t cnode( G[cur.prod][0], {cur.from, cur.set} );
		vector<nidx_t> nxtlits;
		sbl_chd_forest(cur, nxtlits, cur.from, ambset );
		pfgraph[cnode] = ambset;
		for ( auto &aset: ambset )
			for( const nidx_t& nxt: aset) {
				forest( nxt);
			}
	}	
	return true;
}

earley::node_children earley::get_children(const nidx_t nd, bool all=0) const {
	node_children nc;
	auto label = [this](const nidx_t p, bool all=1) {
		return p.nt() ? d.get(p.n()) : (all ? string{ p.c() } : "");
	};
	auto it = pfgraph.find(nd);
	if (it == pfgraph.end()) return nc;
	auto &packset = it->second;
	bool amb = packset.size() > 1;
	size_t c = 0;
	if (amb) o::inf() << "\n'" << label(nd) <<"' is ambiguous:";
	bool picked = false;
	for (auto &pack : packset) {
		if (amb) o::inf() << "\n\tpack " << ++c << ":\t";
		for (auto &p : pack) {
			if (!picked) nc.push_back(std::pair<std::string, const nidx_t>(
				p.nt() ? d.get(p.n())
					: (all ? string{ p.c() } : ""), p));
			if (amb) o::inf() << "'" << (p.nt() ? d.get(p.n())
				: string{ p.c() }) << "' ";
		}
		picked = true;
	}
	return nc;
}

std::string earley::flatten(std::string label, const nidx_t p) {
	stringstream ss;
	node_children nc = get_children(p, true);
	if (nc.size())
		for (auto &c : nc) ss << flatten(c.first, c.second);
	else if (label.size()) ss << label;
	return ss.str();
}

void earley::elem_to_raw_term(raw_term& rt, const nidx_t p) {
	for (auto &c : get_children(p, true)) {
		elem::etype t = elem::NONE;
		if      (c.first == "sym")         t = elem::SYM;
		else if (c.first == "number")      t = elem::NUM;
		else if (c.first == "var")         t = elem::VAR;
		else if (c.first == "quoted_char") t = elem::CHR;
		else if (c.first == "string")      t = elem::STR;
		std::string f = flatten("", c.second);
		if (t == elem::NUM) {
			int_t r = stoll(f);
			if (to_string_(r) != f) { DBGFAIL; } // number reading parse error
			rt.e.emplace_back(r);
		} else if (t == elem::CHR) {
			char32_t ch = f[0];
			if (ch == '\\' && f.size() > 1) switch (f[1]) {
				case 'r': ch = U'\r'; break;
				case 'n': ch = U'\n'; break;
				case 't': ch = U'\t'; break;
				case '\\':ch = U'\\'; break;
				case '\'':ch = U'\''; break;
			}
			rt.e.emplace_back(ch);
		} else
			rt.e.emplace_back(t, dict->get_lexeme(flatten("", c.second)));
	}
}

void earley::args_to_raw_term(raw_term& rt, const nidx_t p) {
	for (auto &c : get_children(p, true))
		if     (c.first == "args" ||
			c.first == "elems" ||
			c.first == "elems_rest")
				args_to_raw_term(rt, c.second);
		else if (c.first == "(") rt.e.emplace_back(elem::OPENP); 
		else if (c.first == ")") rt.e.emplace_back(elem::CLOSEP);
		else if (c.first == "elem") elem_to_raw_term(rt, c.second);
}

raw_term earley::to_raw_term(const nidx_t p) {
	raw_term rt;
	for (auto &c : get_children(p))
		if (c.first == "relname") {
			std::string relname = flatten("", c.second);
			rt.e.emplace_back(elem::SYM, dict->get_lexeme(relname));
		} else if (c.first == "args")
			args_to_raw_term(rt, c.second);
	rt.calc_arity(0);
	return rt;
}

raw_term earley::pred_to_raw_term(const nidx_t p) {
	raw_term rt;
	for (auto c : get_children(p)) {
		if (c.first == "term") rt = to_raw_term(c.second);
		else if (c.first == "negative_term") {
			rt = pred_to_raw_term(c.second);
			rt.neg = true;
		}
	}
	return rt;
}

void earley::add_fact(raw_prog &rp, const nidx_t p) {
	for (auto c : get_children(p))
		if (c.first == "pred")
			rp.r.push_back(raw_rule(pred_to_raw_term(c.second)));	
}

void earley::preds_to_raw_rule(raw_rule &rr, bool h, const nidx_t p) {
	for (auto c : get_children(p)) {
		if (c.first == "preds_rest") preds_to_raw_rule(rr, h, c.second);
		else if (c.first == "pred") {
			raw_term rt = pred_to_raw_term(c.second);
			if (h) rr.h.push_back(rt);
			else {
				if (rr.b.empty()) rr.b.emplace_back();
				rr.b.back().push_back(rt);
			}
		}
	}
}

void earley::add_rule(raw_prog &rp, const nidx_t p) {
	raw_rule rr;
	bool head = true;
	for (auto c : get_children(p))
		if (c.first == "preds")
			preds_to_raw_rule(rr, head, c.second),
			head = false;
	rp.r.push_back(rr);
}

void earley::add_statements(raw_prog &rp, const nidx_t p) {
	for (auto c : get_children(p))
		if (c.first == "statements" || c.first == "statement")
			add_statements(rp, c.second);
		else if (c.first == "rule") add_rule(rp, c.second);
		else if (c.first == "fact") add_fact(rp, c.second);
}

raw_prog earley::to_raw_prog(const nidx_t nd) {
	raw_prog rp;
	add_statements(rp, nd);
	return rp;
}

raw_progs earley::get_raw_progs(dict_t* dct) {
	dict = dct;
	raw_progs rps;
	// find 'start' node
	auto it = pfgraph.begin();
	for ( ; it != pfgraph.end() &&
		!(it->first.nt() && d.get(it->first.n()) == "start"); ++it) ;
	if (it != pfgraph.end()) {
		node_children nc = get_children(it->first);
		for (auto c : get_children(it->first))
			if (c.first == "prog") {
				raw_prog rp = to_raw_prog(c.second);
				rps.p.nps.push_back(rp);
			}
	}
	return rps;
}
