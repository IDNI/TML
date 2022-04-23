#include <unordered_set>
#include "earley.h"
using
	std::vector,
	std::map,
	std::pair,
	std::set,
	std::variant,
	std::basic_string,
	std::basic_ostream,
	std::basic_stringstream,
	std::basic_ostringstream,
	std::endl;

basic_ostream<char32_t>& operator<<(basic_ostream<char32_t>& ss, const char* c){
	return ss << to_u32string(to_string_t(c));
}

basic_ostream<char32_t>& operator<<(basic_ostream<char32_t>& ss, const std::string& s){
	return ss << to_u32string(to_string_t(s));
}

template<typename CharT>
ostream_t& operator<<(ostream_t& os,
	const vector<typename earley<CharT>::string>& v)
{
	for (auto &s : v) if (s.size()) os << s << ' '; else os << "ε ";
	return os;
}

#ifdef DEBUG
template <typename CharT>
ostream_t& operator<<(ostream_t& os, const typename earley<CharT>::lit& l) {
	if (l.nt()) return os << l.n();
	else return os << (l.c() == '\0' ? 'e' : l.c());
}

template <typename CharT>
ostream_t& operator<<(ostream_t& os, const vector<typename earley<CharT>::lit>& v) {
	int i = 0;
	for (auto &l : v) os << l, i++ == 0 ? os << "->": os <<' ';
	return os;
}
#endif

template <typename CharT>
bool earley<CharT>::all_nulls(const vector<lit>& p) const {
	for (size_t k = 1; k != p.size(); ++k)
		if ((!p[k].nt() && p[k].c() != (CharT) '\0') || (p[k].nt() &&
			nullables.find(p[k].n()) == nullables.end()))
			return false;
	return true;
}

template <typename CharT>
earley<CharT>::earley(const vector<production> &g, const char_builtins_map& bm,
	bool _bin_lr) : bin_lr(_bin_lr)
{
	set<string> nt;
	map<string, int_t> bmi;
	for (auto& bmp : bm) {
		d.get(bmp.first);
		nt.insert(bmp.first);
		bmi.emplace(bmp.first, builtins.size());
		builtins.push_back(bmp.second);
		builtin_char_prod.emplace_back();
	}
	auto tostr = [this](const string_t &s) {
		std::basic_ostringstream<CharT> os;
		for (auto &c : s) os << (CharT) c;
		return os.str();
	};
	for (const auto &x : g) nt.insert(tostr(x.p[0].to_str_t()));
	for (const auto &x : g) {
		G.emplace_back();
		for (auto &y : x.p) {
			auto s = tostr(y.to_str_t());
			if (y.type == elem::SYM && nt.find(s) != nt.end()) {
				G.back().emplace_back(d.get(s));
				auto it = bmi.find(s);					
				if (it != bmi.end()) G.back().back()
					.builtin = it->second;
			} else if (x.p.size() == 2 &&
				s == string{ 'n', 'u', 'l', 'l' })
					G.back().emplace_back((CharT) '\0');
			else for (CharT c : s)
				G.back().emplace_back((CharT) c);
		}
	}
	start = lit(d.get(string{ 's', 't', 'a', 'r', 't' }));
	for (size_t n = 0; n != G.size(); ++n) nts[G[n][0]].insert(n);
	size_t k;
	do {
		k = nullables.size();
		for (const auto& p : G)
			if (all_nulls(p))
				nullables.insert(p[0].n());
	} while (k != nullables.size());
#ifdef DEBUG
	o::dbg() << endl << "grammar begin" << endl;
	for (auto x : G) {
		int i = 0;
		for (auto &l : x)
			o::dbg() << to_string(to_string_t(to_str(l))),
			i++ == 0 ? o::dbg() << "->" : o::dbg() << ' ';
		for (auto y : x)
			o::dbg() << to_string(to_string_t(to_str(y)));
		//o::dbg() << ": " << x 
		o::dbg() << endl;
	}
	o::dbg() << endl << "grammar end" << endl;
	o::dbg() << endl << "dictionary start" << endl;
	for (auto x : d.m) o::dbg() << to_string(to_string_t(x.first)) << ' ' <<
		x.second << endl;
	o::dbg() << endl << "dictionary end " << endl;
#endif
}

template <typename CharT>
earley<CharT>::earley(const vector<pair<string, vector<vector<string>>>>& g,
	const char_builtins_map& bm, bool _bin_lr) : bin_lr(_bin_lr)
{
	set<string> nt;
	map<string, int_t> bmi;
	for (auto& bmp : bm) {
		d.get(bmp.first);
		nt.insert(bmp.first);
		bmi.emplace(bmp.first, builtins.size());
		builtins.push_back(bmp.second);
		builtin_char_prod.emplace_back();
	}
	for (const auto &x : g) nt.insert(x.first);
	for (const auto &x : g)
		for (auto &y : x.second) {
			G.push_back({lit(d.get(x.first))});
			for (auto &s : y)
				if (nt.find(s) != nt.end()) {
					G.back().emplace_back(d.get(s));
					auto it = bmi.find(s);					
					if (it != bmi.end()) G.back().back()
						.builtin = it->second;
				} else if (s.size() == 0)
					G.back().emplace_back((CharT) '\0');
				else for (CharT c : s)
					G.back().emplace_back(c);

	}
	start = lit(d.get(basic_string<CharT>{ 's', 't', 'a', 'r', 't' }));
	for (size_t n = 0; n != G.size(); ++n) nts[G[n][0]].insert(n);
	size_t k;
	do {
		k = nullables.size();
		for (const auto& p : G)
			if (all_nulls(p))
				nullables.insert(p[0].n());
	} while (k != nullables.size());
#ifdef DEBUG
	o::dbg() << "g: \n";
	for (auto x : g)
		for (auto y : x.second) {
			o::dbg() <<'\t'<< to_string(to_string_t(x.first)) <<'=';
			for (auto z : y) o::dbg() << to_string(to_string_t(z));
			o::dbg() << endl;
		}
	// o::dbg() << "G:\n";
	// for (auto x : G) {
	// 	o::dbg() << '\t';
	// 	//for (auto y : x) o::dbg() << y << " ";
	// 	o::dbg() << endl;
	// }
	o::dbg() << "d.m:\n";
	for (auto x : d.m) o::dbg() << '\t' << to_string(to_string_t(x.first)) << ' '<< x.second << endl;
#endif
}

template <typename CharT>
std::basic_ostream<CharT>& earley<CharT>::print(std::basic_ostream<CharT>& os, const item& i) const {
	os << i.set << " " << i.from << " ";
	for (size_t n = 0; n != G[i.prod].size(); ++n) {
		if (n == i.dot) os << "* ";
		if (G[i.prod][n].nt()) os << d.get(G[i.prod][n].n()) << " ";
		else if (G[i.prod][n].c() == (CharT) '\0') os << "ε " << " ";
		else os << G[i.prod][n].c() << " ";
	}
	if (G[i.prod].size() == i.dot) os << "*";
	return os;
}

template <typename CharT>
typename set<typename earley<CharT>::item>::iterator earley<CharT>::add(set<item>& t, const item& i) {
	//DBG(print(o::dbg() << "adding ", i) << endl;)
	auto it = S.find(i);
	if (it != S.end()) return it;
	if ((it = t.find(i)) != t.end()) return it;
	it = t.insert(i).first;
	if (nullable(*it))
		add(t, item(it->set, it->prod, it->from, it->dot + 1));
			//->advancers.insert(i);
	return it;
}

template <typename CharT>
void earley<CharT>::complete(const item& i, set<item>& t) {
	//DBG(print(o::dbg() << "completing ", i) << endl;)
	for (	auto it = S.lower_bound(item(i.from, 0, 0, 0));
		it != S.end() && it->set == i.from; ++it)
		if (	G[it->prod].size() > it->dot &&
			get_lit(*it) == get_nt(i))
			add(t, item(i.set, it->prod, it->from, it->dot + 1));
				//completers.insert(i);
}

template <typename CharT>
void earley<CharT>::predict(const item& i, set<item>& t) {
	//DBG(print(o::dbg() << "predicting ", i) << endl;)
	for (size_t p : nts[get_lit(i)]) {
		item j(i.set, p, i.set, 1);
		add(t, j); //->advancers.insert(i);
		//DBG(print(o::dbg() << "predicting added ", j) << endl;)
	}
}

template <typename CharT>
void earley<CharT>::scan_builtin(const item& i, size_t n, CharT ch) {
	int_t bid = get_lit(i).builtin;
	if (!builtins[bid](ch)) return; // character is not in the builtin class
	size_t p = 0; // character's prod rule
	auto it = builtin_char_prod[bid].find(ch);
	if (it == builtin_char_prod[bid].end()) {
		p = G.size(); // its a new character in this builtin -> store it 
		G.push_back({ get_lit(i) });
		G.back().emplace_back(ch);
		builtin_char_prod[bid][ch] = p; // store prod of this ch
	} else p = it->second; // this ch has its prod already
	item j(n + 1, i.prod, n, 2); // complete builtin
	S.insert(j);
	item k(n + 1, p, n, 2);      // complete builtin's character
	S.insert(k);
}

template <typename CharT>
void earley<CharT>::scan(const item& i, size_t n, CharT ch) {
	if (ch != get_lit(i).c()) return;
	item j(n + 1, i.prod, i.from, i.dot + 1);
	S.insert(j);
	//first->advancers.insert(i);
	//DBG(print(o::dbg(), i) << ' ';)
	//DBG(print(o::dbg() << "scanned " << ch << " and added ", j) << "\n";)
	/*
	stringstream ss;
	ss<<" encountered '"<<ch <<"' at position "<< n <<", try '"<<get_lit(i).c() << "' instead";
	parse_error( 0, ss.str().c_str() );	
	*/
}

template <typename CharT>
bool earley<CharT>::recognize(const typename earley<CharT>::string s) {
	DBG(bool pms = o::enabled("parser-benchmarks");)
	//DBG(o::dbg() << "recognizing: " << to_string(to_string_t(s)) << endl;)
	emeasure_time_start(tsr, ter);
	inputstr = s;
	size_t len = s.size();
	S.clear();//, S.resize(len + 1);//, C.clear(), C.resize(len + 1);
	for (size_t n : nts[start]) S.emplace(0, n, 0, 1);
	set<item> t;
#ifdef DEBUG
	size_t r = 1, cb = 0; // row and cel beginning
#endif
	for (size_t n = 0; n != len + 1; ++n) {
#ifdef DEBUG
		if (s[n] == '\n') (cb = n), r++;
		emeasure_time_start(tsp, tep);
#endif
		do {
			S.insert(t.begin(), t.end());
			t.clear();
			for (	auto it = S.lower_bound(item(n, 0, 0, 0));
				it != S.end() && it->set == n; ++it) {
				//DBG(print(o::dbg() << "processing ", *it) << endl;)
				if (completed(*it)) complete(*it, t);
				else if (get_lit(*it).is_builtin()) {
					if (n < len) scan_builtin(*it, n, s[n]);
				} else if (get_lit(*it).nt()) predict(*it, t);
				else if (n < len) scan(*it, n, s[n]);
			}
		} while (!t.empty());
#ifdef DEBUG
		if (pms) {
			o::pms()<<n<<" \tln: "<<r<<" col: "<<(n-cb+1)<<" :: ";
			emeasure_time_end(tsp, tep)<<"\n";
		}
#endif
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
	emeasure_time_end( tsr, ter ) <<" :: recognize time" <<endl;
	forest();
	return found;
}

template <typename CharT>
std::string earley<CharT>::grammar_text() {
	std::stringstream txt;
	for (const auto &p : G) {
		txt << "\n\\l";
		size_t i = 0;
		for( const auto &l : p){
			if (l.nt()) txt << to_string(to_string_t(d.get(l.n())));
			else if (l.c() != '\0')
				txt << to_string(to_string_t((CharT)l.c())),
				COUT << "\tgrammar_text - c: `" << to_string(to_string_t((CharT)l.c())) << "`\n";
			else txt << "ε";
			txt <<  " ";
			if (i++ == 0) txt << "-> ";
		}
	}
	return txt.str();
}

template <typename CharT>
bool earley<CharT>::to_tml_facts(ostream_t& ss) const {
	auto str_rel_output = [&ss] (string rel, size_t id,
		vector<variant<size_t, typename earley<CharT>::string>> args)
	{
		ss << to_string(to_string_t(rel)) << "("<< id;
		for (auto &a : args) {
			if (std::holds_alternative<size_t>(a))
				ss << " " << std::get<size_t>(a);
			else    ss << " " << to_string(to_string_t(
							std::get<string>(a)));
#ifdef DEBUG
			if (std::holds_alternative<size_t>(a))
				o::dbg() << " " << std::get<size_t>(a);
			else o::dbg() << " " << to_string(to_string_t(
							std::get<string>(a)));
#endif
		}
		ss << ").\n";
	};
	visit_forest(str_rel_output);
	return true;
}

template <typename CharT>
template <typename T>
bool earley<CharT>::visit_forest(T out_rel) const {
//bool earley::visit_forest(std::function<void(std::string,size_t, std::vector<std::variant<size_t, std::string>>)> out_rel) const{
	std::stringstream ss;
	auto get_args = [this] (const nidx_t & k){
		arg_t args;
		if (k.nt()) args.emplace_back(
			string{ '"' } + d.get(k.n()) + string{ '"' });
		else if (k.c() == (CharT) '\0' ) args.emplace_back(epsilon());
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
		//DBG(assert(it.second.size()!= 0));
		id++;
	}
	ss<<std::endl;
	string node_s{ 'n', 'o', 'd', 'e' }, edge_s{ 'e', 'd', 'g', 'e' };
	for( auto &it: pfgraph ) {
		arg_t ndesc = get_args(it.first);
		out_rel(node_s, nid[it.first], ndesc);
		size_t p = 0;
		for( auto &pack : it.second) {
			if(it.second.size() > 1) {  //skipping if only one ambigous node, an optimization
				++p;
				out_rel(edge_s, nid[it.first], { nid[it.first] + p } );
				out_rel(node_s, nid[it.first] + p, {} );
			}
			for( auto & nn: pack) {
				if(nid.find(nn) == nid.end()) nid[nn] = id++; // for terminals, not seen before
				arg_t nndesc = get_args(nn);
				out_rel(node_s, nid[nn], nndesc );
				out_rel(edge_s, nid[it.first] + p, {nid[nn]} );
			}
		}
	}
	return true;
}
template <typename CharT>
size_t earley<CharT>::count_parsed_trees() const{
	nidx_t root(start, {0, inputstr.length()});
	std::unordered_set<nidx_t, hasher_t> done;
	return _count_parsed_trees(root, done);

}

template <typename CharT>
size_t earley<CharT>::_count_parsed_trees(const nidx_t &root, 
					std::unordered_set<nidx_t, hasher_t> &done ) const{
	
	if( !root.nt() ) return 1;
	else if( pfgraph.find(root) == pfgraph.end() ) return 0;
	auto &pack =  pfgraph.find(root)->second;
	size_t count = pack.size();
	done.insert(root);
	for( const auto &nodes: pack)
		for( const auto &chd: nodes)
		if(chd.nt() && !done.count(chd)) 
			count *= _count_parsed_trees(chd, done);
	return count;
}


template <typename CharT>
vector<typename earley<CharT>::arg_t> earley<CharT>::get_parse_graph_facts(){
	vector<arg_t> rts;
	auto rt_rel_output = [&rts] (string rel, size_t id, vector<variant<size_t, string>> args){
		args.insert(args.begin(), {rel, id });
		rts.emplace_back(args);
	};
	visit_forest(rt_rel_output);
	return rts;
}

template <typename CharT>
std::string earley<CharT>::to_tml_rule(const nidx_t nd) const {
	std::stringstream ss;
	if (nd.l.nt()) ss << to_string(to_string_t(d.get(nd.l.n())));
	else if (nd.l.c() == (CharT) '\0') ss << "ε";
	else ss << to_string(to_string_t(nd.l.c()));
	ss << "(" << nd.span.first << " " << nd.span.second << ")";
	return ss.str();
}

template <typename CharT>
bool earley<CharT>::to_tml_rule(ostream_t& ss) const{
	set<std::string> terminals;
	for (auto &it: pfgraph ) {
		for (auto &pack : it.second) { 
			ss << to_tml_rule(it.first) << ":-";
			for (size_t i = 0; i < pack.size(); i++) {
				// if terminal
				if (pfgraph.find(pack[i]) == pfgraph.end())
					terminals.insert(to_tml_rule(pack[i]));
				ss << to_tml_rule(pack[i])
					<< (i == pack.size()-1 ? "." : ",");
			};
			ss << "\n";
		}
	}
	for (auto &t: terminals) ss << t << ".\n";
	return true;
}

template <typename CharT>
std::string earley<CharT>::to_dot_safestring(const string &s) const {
	return to_string(to_string_t(s));
}

template <typename CharT>
bool earley<CharT>::to_dot(ostream_t& ss) {
	auto keyfun = [this] (const nidx_t & k){
		std::stringstream l;
		k.nt() ? l << to_string(to_string_t(d.get(k.n())))
			: k.c() == '\0' ? l << "ε"
				: l << to_string(to_string_t(k.c()));
		l << "_" << k.span.first << "_" << k.span.second << "_";
		std::string desc = l.str();
		return std::pair<size_t, std::string>(
			std::hash<std::string>()(desc), desc);
	};
	ss << "digraph {\n";
	ss << "_input_" << "[label =\"" << to_string(to_string_t(inputstr)) <<
		"\", shape = rectangle]" ;
	ss << "_grammar_" << "[label =\"" << grammar_text() <<
		"\", shape = rectangle]" ;
	ss << "\nnode" << "[ ordering =\"out\"];";
	ss << "\ngraph" << "[ overlap =false, splines = true];";

	std::unordered_set<std::pair<size_t,size_t>, hasher_t> edgedone;
	edgedone.clear();
	for (auto &it: pfgraph) {
		auto key = keyfun(it.first);
		ss << "\n" << key.first << "[label=\"" << key.second <<"\"];";
		size_t p = 0;
		std::stringstream pstr;
		for (auto &pack : it.second) {
			pstr<<key.second<<p++;
			auto ambkey = std::hash<std::string>()(pstr.str());
			ss << "\n" << ambkey << "[shape = point,label=\"" <<
				pstr.str() << "\"];";
			if(edgedone.insert({ key.first, ambkey }).second )
				ss << "\n" << key.first << "->" << ambkey <<';';
			for (auto & nn: pack) {
				auto nkey = keyfun(nn);
				ss << "\n" << nkey.first << "[label=\"" <<
					nkey.second << "\"];";
				if (edgedone.insert({ ambkey, nkey.first })
					.second) ss << "\n" << ambkey << "->" <<
						nkey.first<< ';';
			}
			pstr.str({});
		}
	}
	ss << "\n}\n";
	return true;
}

// collects all possible variations of the given item's rhs while respecting the span of the item
// and stores them in the set ambset. 
template <typename CharT>
void earley<CharT>::sbl_chd_forest( const item &eitem, std::vector<nidx_t> &curchd, size_t xfrom, std::set<std::vector<nidx_t>> &ambset  ) {

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
		if( nxtl.c() == (CharT) '\0') nxtl.span.second = xfrom;
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
		
		//auto &nxtl_froms = sorted_citem[nxtl.n()][xfrom];
		auto &nxtl_froms = sorted_citem[{nxtl.n(),xfrom}];
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
template <typename CharT>
bool earley<CharT>::forest( ){
	bool ret = false;
	// clear forest structure if any
	pfgraph.clear();
	bin_tnt.clear();
	// set the start root node
	size_t len = inputstr.length();
	nidx_t root(start, {0,len});
	// preprocess earley items for faster retrieval
	emeasure_time_start(tspfo, tepfo);
	int count = 0;
	for (const item& i : S) { 
		count++;
			//sorted_citem[G[i.prod][0].n()][i.from].emplace_back(i);
		if( completed(i) )
			sorted_citem[{G[i.prod][0].n(), i.from}].emplace_back(i),
			rsorted_citem[{G[i.prod][0].n(), i.set}].emplace_back(i);
		else if(bin_lr) {
			static size_t tid=0;
			if( i.dot >= 3 ){
				std::vector<lit> v(G[i.prod].begin()+1, G[i.prod].begin()+i.dot);
				lit tlit;
				if(bin_tnt.find(v) == bin_tnt.end()) {
					stringstream ss;
					ss << "temp" << tid++;
					tlit = lit(d.get(ss.str()));
					bin_tnt.insert({v, tlit});
				}
				else tlit = bin_tnt[v];
				
				//DBG(print(o::dbg(), i);)
				//o::dbg()<< endl << d.get(tlit.n()) << v << endl;
				sorted_citem[{tlit.n(), i.from}].emplace_back(i),
				rsorted_citem[{tlit.n(), i.set}].emplace_back(i);
			}
		}
	}

	emeasure_time_end(tspfo, tepfo) <<" :: preprocess time ,"<< "size : "<< count << endl;
	o::inf() <<"sort sizes : " << sorted_citem.size() <<" " << rsorted_citem.size() <<" \n";
	// build forest
	emeasure_time_start(tsf, tef);
	if(bin_lr)
		ret = build_forest2(root);
	else 
		ret = build_forest(root);
	emeasure_time_end(tsf, tef) <<" :: forest time "<<endl ;

	o::inf() <<"# parse trees " << count_parsed_trees() <<endl;

	// emit output in various formats
	if (o::enabled("parser-to-dot")) {	
		emeasure_time_start(tsf1, tef1);
		to_dot(o::to("parser-to-dot")),
		emeasure_time_end(tsf1, tef1) << ":: to dot time\n";
	}
	if (o::enabled("parser-to-tml")) {
		emeasure_time_start(tsf2, tef2);
		to_tml_facts(o::to("parser-to-tml")),
		emeasure_time_end(tsf2, tef2) << ":: to tml time\n";
	}
	if (o::enabled("parser-to-rules")) {
		emeasure_time_start(tsf3, tef3);
		to_tml_rule(o::to("parser-to-rules")),
		emeasure_time_end(tsf3, tef3) << ":: to rules time\n";
	}

	return ret; 
}
template <typename CharT>
bool earley<CharT>::bin_lr_comb(const item& eitem, std::set<std::vector<nidx_t>>& ambset) {

	std::vector<nidx_t> rcomb, lcomb;
	if( eitem.dot < 2  ) return false;

	nidx_t right = G[eitem.prod][eitem.dot-1];

	if(!right.nt()) {
		right.span.second = eitem.set;
		if( right.c() == (CharT) '\0') right.span.first = right.span.second;
		else if (inputstr.at(eitem.set -1) == right.c() )
			right.span.first = eitem.set -1 ;
		else return false;
		rcomb.emplace_back(right);
	}
	else {
		auto &rightit = rsorted_citem[{right.n(), eitem.set}];
		for( auto &it : rightit)
			if( eitem.from <= it.from ) 
				right.span.second = it.set, right.span.first = it.from,
				rcomb.emplace_back(right);
	}
	// many literals in rhs
	if(eitem.dot > 3) {
		//DBG(print(o::dbg(), eitem);)
		std::vector<lit> v(G[eitem.prod].begin()+1, G[eitem.prod].begin()+ eitem.dot - 1);
		DBG(assert( bin_tnt.find(v) != bin_tnt.end());)
		nidx_t left = bin_tnt[v];
		//DBG(COUT << std::endl << d.get(bin_tnt[v].n()) << std::endl);
		auto &leftit = sorted_citem[{left.n(), eitem.from}];
		// doing left right optimization
		for(auto &it : leftit) 
			for(auto &rit : rcomb)    
				if(it.set == rit.span.first) {
					left.span.first = it.from;
					left.span.second = it.set;
					ambset.insert({left, rit});
				} 
	}
	// exact two literals in rhs
	else if(eitem.dot == 3 ) {	
		nidx_t left = G[eitem.prod][eitem.dot-2];
		if(!left.nt()) {
			left.span.first = eitem.from;
			if( left.c() == (CharT) '\0') left.span.second = left.span.first;
			else if (inputstr.at(eitem.from) == left.c() )
				left.span.second = eitem.from + 1  ;
			else return false;
			//do Left right optimisation
			for(auto &rit : rcomb)  
				if( left.span.second == rit.span.first)
					ambset.insert({left, rit});
		}
		else {
	 		auto &leftit = sorted_citem[{left.n(), eitem.from}];
			for(auto &it : leftit) 
				for(auto &rit : rcomb)    
					if(it.set == rit.span.first)
						left.span.first = it.from,
						left.span.second = it.set,
						ambset.insert({left, rit});
		}
	}
	else {
		DBG(assert(eitem.dot == 2));
		for(auto &rit : rcomb)    
			if(eitem.from <= rit.span.first)
				ambset.insert({rit});
	}
	return true;
}

// builds the forest starting with root
template <typename CharT>
bool earley<CharT>::build_forest ( const nidx_t &root ) {
	if(!root.nt()) return false;
	if(pfgraph.find(root) != pfgraph.end()) return false;

	//auto &nxtset = sorted_citem[root.n()][root.span.first];
	auto &nxtset = sorted_citem[{root.n(),root.span.first}];
	std::set<std::vector<nidx_t>> ambset;
	for(const item &cur: nxtset) {
		if(cur.set != root.span.second) continue;
		nidx_t cnode( G[cur.prod][0], {cur.from, cur.set} );
		vector<nidx_t> nxtlits;
		sbl_chd_forest(cur, nxtlits, cur.from, ambset );
		pfgraph[cnode] = ambset;
		for ( auto &aset: ambset )
			for( const nidx_t& nxt: aset) {
				build_forest( nxt);
			}
	}	
	return true;
}

template <typename CharT>
bool earley<CharT>::build_forest2 ( const nidx_t &root ) {
	if(!root.nt()) return false;
	if(pfgraph.find(root) != pfgraph.end()) return false;

	//auto &nxtset = sorted_citem[root.n()][root.span.first];
	auto &nxtset = sorted_citem[{root.n(),root.span.first}];
	std::set<std::vector<nidx_t>> ambset;
	for(const item &cur: nxtset) {
		if(cur.set != root.span.second) continue;
		nidx_t cnode( completed(cur) ? G[cur.prod][0]: root.n(),
		 {cur.from, cur.set} );
		bin_lr_comb(cur, ambset);
		pfgraph[cnode] = ambset;
		for ( auto &aset: ambset )
			for( const nidx_t& nxt: aset) {
				build_forest2( nxt);
			}
	}	
	return true;
}

template <typename CharT>
typename earley<CharT>::node_children earley<CharT>::get_children(const nidx_t nd, bool all) const {
	node_children nc;
	auto label = [this](const nidx_t p, bool all=1) {
		return p.nt() ? d.get(p.n()) : (all ? string{ p.c() } : string{});
	};
	auto it = pfgraph.find(nd);
	if (it == pfgraph.end()) return nc;
	auto &packset = it->second;
	bool amb = packset.size() > 1;
	size_t c = 0;
	if (amb) o::inf() << "\n'" << to_string(to_string_t(label(nd, true)))
		<<"' is ambiguous:";
	bool picked = false;
	for (auto &pack : packset) {
		if (amb) o::inf() << "\n\tpack " << ++c << ":\t";
		for (auto &p : pack) {
			if (!picked) nc.push_back(std::pair<string,
				const nidx_t>(label(p, all), p));
			if (amb) o::inf() << "'" << to_string(to_string_t(
				label(p, true))) << "' ";
		}
		picked = true;
	}
	return nc;
}

template <typename CharT>
typename earley<CharT>::string earley<CharT>::flatten(
	earley<CharT>::string label, const nidx_t p) const
{
	stringstream ss;
	node_children nc = get_children(p, true);
	if (nc.size())
		for (auto &c : nc) ss << flatten(c.first, c.second);
	else if (label.size()) ss << label;
	return ss.str();
}



template class earley<char>;
template class earley<char32_t>;

template <>
std::basic_string<char> earley<char>::epsilon()         const { return  "ε"; }
template <>
std::basic_string<char32_t> earley<char32_t>::epsilon() const { return U"ε"; }
