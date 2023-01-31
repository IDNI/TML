// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.

#include <iomanip>
#include <unordered_set>
#include "earley.h"
using
	std::vector,
	std::map,
	std::pair,
	std::set,
	std::variant,
	std::char_traits,
	std::basic_string,
	std::basic_ostream,
	std::basic_stringstream,
	std::basic_ostringstream,
	std::endl;

basic_ostream<char32_t>& operator<<(basic_ostream<char32_t>& ss, const char* c){
	for (const auto& ch: to_u32string(to_string_t(c))) ss.put(ch);
	return ss;
}

basic_ostream<char32_t>& operator<<(basic_ostream<char32_t>& ss,
	const std::string& s)
{
	for (const auto& ch: to_u32string(to_string_t(s))) ss.put(ch);
	return ss;
}

//basic_ostream<char32_t>& operator<<(basic_ostream<char32_t>& ss,const size_t& n)
//{
//	return ss << to_string_(n);
//}
//
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
ostream_t& operator<<(ostream_t& os,
	const vector<typename earley<CharT>::lit>& v)
{
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

template <>
earley<char>::string earley<char>::to_str(const string_t &s) const {
	return to_string(s);	
}

template <>
earley<char32_t>::string earley<char32_t>::to_str(const string_t &s) const {
	return to_u32string(s);
}

template <typename CharT>
earley<CharT>::earley(const vector<production> &g, const char_builtins_map& bm,
	bool _bin_lr, bool _incr_gen_forest) : bin_lr(_bin_lr),
	incr_gen_forest(_incr_gen_forest) { 
	set<string> nt;
	map<string, int_t> bmi;
	for (auto& bmp : bm) {
		d.get(bmp.first);
		nt.insert(bmp.first);
		bmi.emplace(bmp.first, builtins.size());
		builtins.push_back(bmp.second);
		builtin_char_prod.emplace_back();
	}
	for (const auto &x : g) nt.insert(to_str(x.p[0].to_str_t()));
	for (const auto &x : g) {
		G.emplace_back();
		for (auto &y : x.p) {
			auto s = to_str(y.to_str_t());
			if (y.type == elem::SYM && nt.find(s) != nt.end()) {
				G.back().push_back(lit{ d.get(s) });
				auto it = bmi.find(s);
				if (it != bmi.end()) G.back().back()
					.builtin = it->second;
			} else if (x.p.size() == 2 &&
				s == string{ 'n', 'u', 'l', 'l' })
					G.back().push_back(lit{ (CharT) '\0' });
			else for (CharT c : s)
				G.back().push_back(lit{ (CharT) c });
		}
		// add priorities/prefer
		//  .... , #     or   ..... , pref
		if(x.c.size() == 1 && x.c[0].e.size() == 1 ){
			if (x.c[0].e[0].type == elem::NUM)
				priority.insert({G.back(), x.c[0].e[0].num });
			else if (x.c[0].e[0].type == elem::SYM
				&& x.c[0].e[0].to_str_t() == string_t{
						'_', 'p', 'r', 'e', 'f' })
					prefer.insert(G.back());
			else o::err() << "\nIgnoring " << x.c[0] << "\n"; 
		}
		else if (x.c.size() > 1)
			o::err() << "\nIgnoring " << x.c[0] << "...\n";

	}
	start = lit{ d.get(string{ 's', 't', 'a', 'r', 't' }) };
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
			o::dbg() << to_stdstr(to_str(l)),
			i++ == 0 ? o::dbg() << "->" : o::dbg() << ' ';
		for (auto y : x)
			o::dbg() << to_stdstr(to_str(y));
		
		auto it = priority.find(x);
		if( it != priority.end())
			o::dbg() <<" " << it->second;
		if( prefer.count(x))
			o::dbg() <<" _pref";
		//o::dbg() << ": " << x 
		o::dbg() << endl;
	}
	o::dbg() << endl << "grammar end" << endl;
	o::dbg() << endl << "dictionary start" << endl;
	for (auto x : d.m) o::dbg() << to_stdstr(x.first) << ' ' <<
		x.second << endl;
	o::dbg() << endl << "dictionary end " << endl;
#endif
}

template <typename CharT>
earley<CharT>::earley(const vector<pair<string, vector<vector<string>>>>& g,
	const char_builtins_map& bm, bool _bin_lr, bool _incr_gen_forest) :
	 bin_lr(_bin_lr), incr_gen_forest(_incr_gen_forest) {

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
			G.push_back({ lit{ d.get(x.first) } });
			for (auto &s : y)
				if (nt.find(s) != nt.end()) {
					G.back().push_back(lit{ d.get(s) });
					auto it = bmi.find(s);
					if (it != bmi.end()) G.back().back()
						.builtin = it->second;
				} else if (s.size() == 0)
					G.back().push_back(lit{ (CharT) '\0' });
				else for (CharT c : s)
					G.back().push_back(lit{ c });

	}
	start = lit{ d.get(basic_string<CharT>{ 's', 't', 'a', 'r', 't' }) };
	for (size_t n = 0; n != G.size(); ++n) nts[G[n][0]].insert(n);
	size_t k;
	do {
		k = nullables.size();
		for (const auto& p : G)
			if (all_nulls(p)) nullables.insert(p[0].n());
	} while (k != nullables.size());
#ifdef DEBUG
	o::dbg() << "g: \n";
	for (auto x : g)
		for (auto y : x.second) {
			o::dbg() <<'\t'<< to_stdstr(x.first) <<'=';
			for (auto z : y) o::dbg() << to_stdstr(z);
			o::dbg() << endl;
		}
	// o::dbg() << "G:\n";
	// for (auto x : G) {
	// 	o::dbg() << '\t';
	// 	//for (auto y : x) o::dbg() << y << " ";
	// 	o::dbg() << endl;
	// }
	o::dbg() << "d.m:\n";
	for (auto x : d.m) o::dbg() <<
		'\t' << to_stdstr(x.first) << ' ' << x.second << endl;
#endif
}

template <typename CharT>
typename earley<CharT>::ostream& earley<CharT>::print(
	earley<CharT>::ostream& os, const item& i) const
{
	put(put(os, i.set) << " ", i.from) << " ";
	for (size_t n = 0; n != G[i.prod].size(); ++n) {
		if (n == i.dot) os << "* ";
		if (G[i.prod][n].nt()) put(os, d.get(G[i.prod][n].n())) << " ";
		else if (G[i.prod][n].c() == (CharT) '\0') os << "ε " << " ";
		else put(os, G[i.prod][n].c()) << " ";
	}
	if (G[i.prod].size() == i.dot) os << "*";
	return os;
}

template <typename CharT>
typename earley<CharT>::container_iter earley<CharT>::add(container_t& t, 
		const item& i) {
	//DBG(print(o::dbg() << "adding ", i) << endl;)
	auto& cont = S[i.set];
	auto it = cont.find(i);
	if (it != cont.end()) return it;
	if ((it = t.find(i)) != t.end()) return it;
	it = t.insert(i).first;
	if (nullable(*it))
		add(t, item(it->set, it->prod, it->from, it->dot + 1));
			//->advancers.insert(i);
	return it;
}

template <typename CharT>
void earley<CharT>::complete(const item& i, container_t& t) {
	//DBG(print(o::dbg() << "completing ", i) << endl;)
	const container_t& cont = S[i.from];
	for (auto it = cont.begin(); it != cont.end(); ++it)
		if (G[it->prod].size() > it->dot &&
			get_lit(*it) == get_nt(i))
			add(t, item(i.set, it->prod, it->from, it->dot + 1));
				//completers.insert(i);
}

template <typename CharT>
void earley<CharT>::predict(const item& i, container_t& t) {
	//DBG(print(o::dbg() << "predicting ", i) << endl;)
	for (size_t p : nts[get_lit(i)]) {
		item j(i.set, p, i.set, 1);
		add(t, j); //->advancers.insert(i);
		//DBG(print(o::dbg() << "predicting added ", j) << endl;)
	}
}

template <typename CharT>
void earley<CharT>::scan_builtin(const item& i, size_t n, const string& s) {
	size_t p = 0; // character's prod rule
	int_t bid = get_lit(i).builtin;
	bool eof = n == s.size();
	CharT ch = eof ? std::char_traits<CharT>::eof() : s[n];
	auto it = builtin_char_prod[bid].find(ch);
	if (it == builtin_char_prod[bid].end()) {
		if (!builtins[bid](ch)) return; //char isn't in the builtn class
		p = G.size(); // its a new character in this builtin -> store it 
		G.push_back({ get_lit(i) });
		G.back().push_back(lit{ ch });
		builtin_char_prod[bid][ch] = p; // store prod of this ch
	} else p = it->second; // this ch has its prod already
	item j(n + !eof, i.prod, n, 2); // complete builtin
	S[j.set].insert(j);
	item k(n + !eof, p, n, 2);      // complete builtin's character
	S[k.set].insert(k);
}

template <typename CharT>
void earley<CharT>::scan(const item& i, size_t n, CharT ch) {
	if (ch != get_lit(i).c()) return;
	item j(n + 1, i.prod, i.from, i.dot + 1);
	S[j.set].insert(j);
	//first->advancers.insert(i);
	//DBG(print(o::dbg(), i) << ' ';)
	//DBG(print(o::dbg() << "scanned " << ch << " and added ", j) << "\n";)
	/*
	stringstream ss;
	ss<<" encountered '"<<ch <<"' at position "<< n <<", try '"<<
		get_lit(i).c() << "' instead";
	parse_error( 0, ss.str().c_str() );	
	*/
}

template <typename CharT>
bool earley<CharT>::recognize(const typename earley<CharT>::string s) {
	DBG(bool pms = o::enabled("parser-benchmarks");)
	//DBG(o::dbg() << "recognizing: " << to_stdstr(s) << endl;)
	emeasure_time_start(tsr, ter);
	inputstr = s;
	size_t len = s.size();
	pfgraph.clear();
	bin_tnt.clear();
	tid = 0;
	S.clear();//, S.resize(len + 1);//, C.clear(), C.resize(len + 1);
	S.resize(len+1);
	for (size_t n : nts[start]) {
		auto& cont = S[0];
		auto it = cont.emplace(0, n, 0, 1).first;
		// fix the bug for missing Start( 0 0) when start is nulllable
		if(nullable(*it))
			cont.emplace(0, n, 0, 2);
	}
	container_t t;
#ifdef DEBUG
	size_t r = 1, cb = 0; // row and cel beginning
#endif
	for (size_t n = 0; n != len + 1; ++n) {
#ifdef DEBUG
		if (s[n] == '\n') (cb = n), r++;
		emeasure_time_start(tsp, tep);
#endif
		do {
			for(const item &x : t) S[x.set].insert(x);
			t.clear();
			const auto& cont = S[n];
			for (auto it = cont.begin();
				it != cont.end(); ++it) {
				//DBG(print(o::dbg() << "processing ", *it) << endl;)
				if (completed(*it)) complete(*it, t);
				else if (get_lit(*it).is_builtin()) {
					if (n <= len) scan_builtin(*it, n, s);
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
		if (true == incr_gen_forest) {
		DBG(o::dbg() << "set: " << n << endl;)
		const auto& cont = S[n];
		for (auto it = cont.begin(); it != cont.end(); ++it)
			if(completed(*it)) pre_process(*it);
			
		for (auto it = cont.begin(); it != cont.end(); ++it)
			if (completed(*it)) { 
				DBG(o::dbg()<<endl<< it->from <<it->set << 
					it->prod << it->dot <<endl);				
				nidx_t curroot(get_nt(*it), {it->from, it->set});
				build_forest(curroot);
				//to_tml_rule(o::to("parser-to-rules"));
			}
		}
	}
	bool found = false;
	for (size_t n : nts[start])
		if (S[len].find( item(len, n, 0, G[n].size())) != S[len].end()) 
			found = true;
	emeasure_time_end(tsr, ter) <<" :: recognize time" <<endl;
	if(!incr_gen_forest) forest();
	ptree_t pt;
	//this->get_parsed_tree();

	if (o::enabled("parser-to-rules")) {
		emeasure_time_start(tsf3, tef3);
		to_tml_rule(o::to("parser-to-rules"), pt),
		emeasure_time_end(tsf3, tef3) << ":: to rules time\n";
	}
	if (o::enabled("parser-to-dot")) {	
		emeasure_time_start(tsf1, tef1);
		to_dot(o::to("parser-to-dot"), pt),
		emeasure_time_end(tsf1, tef1) << ":: to dot time\n";
	}
	if (o::enabled("parser-to-tml")) {
		emeasure_time_start(tsf2, tef2);
		to_tml_facts(o::to("parser-to-tml"), pt),
		emeasure_time_end(tsf2, tef2) << ":: to tml time\n";
	}
	return found;
}

template <typename CharT>
template <typename T>
bool earley<CharT>::to_tml_facts(ostream_t& ss, T &&pt) const {
	auto str_rel_output = [&ss, this] (string rel, size_t id,
		vector<variant<size_t, typename earley<CharT>::string>> args)
	{
		ss << to_stdstr(rel) << "(" << id;
		for (auto &a : args) {
			if (std::holds_alternative<size_t>(a))
				ss << " " << std::get<size_t>(a);
			else    ss << " " << to_stdstr(std::get<string>(a));
#ifdef DEBUG
			if (std::holds_alternative<size_t>(a))
				o::dbg() << " " << std::get<size_t>(a);
			else o::dbg() << " " << to_stdstr(std::get<string>(a));
#endif
		}
		ss << ").\n";
	};
	iterate_forest(str_rel_output, pt);
	return true;
}

template <typename CharT>
template <typename T, typename P>
bool earley<CharT>::iterate_forest(T out_rel, P &&pt) const {
	std::stringstream ss;
	auto get_args = [this] (const nidx_t & k){
		arg_t args;
		if (k.nt()) args.emplace_back(
			string{ '"' } + d.get(k.n()) + string{ '"' });
		else if (k.c() == (CharT) '\0' ) args.emplace_back(epsilon());
		else args.emplace_back(string({ '"', k.c(), '"' }));
		args.emplace_back(k.span.first);
		args.emplace_back(k.span.second);
		return args;
	};

	map<nidx_t, size_t> nid;
	size_t id = 0;
	for (auto &it: pt.size() ? pt : pfgraph) {
		nid[it.first] = id;
		// skip ids for one child ambig node
		id += it.second.size()== 1 ? 0 : it.second.size(); // ambig node ids;
		//DBG(assert(it.second.size()!= 0));
		id++;
	}
	ss << std::endl;
	string node_s{ 'n', 'o', 'd', 'e' }, edge_s{ 'e', 'd', 'g', 'e' };
	for (auto &it : pt.size()? pt : pfgraph) {
		arg_t ndesc = get_args(it.first);
		out_rel(node_s, nid[it.first], ndesc);
		size_t p = 0;
		for (auto &pack : it.second) {
			if (it.second.size() > 1) {  //skipping if only one ambigous node, an optimization
				++p;
				out_rel(edge_s, nid[it.first],
						{ nid[it.first] + p } );
				out_rel(node_s, nid[it.first] + p, {} );
			}
			for (auto & nn: pack) {
				if (nid.find(nn) == nid.end()) nid[nn] = id++; // for terminals, not seen before
				arg_t nndesc = get_args(nn);
				out_rel(node_s, nid[nn], nndesc);
				out_rel(edge_s, nid[it.first] + p, { nid[nn] });
			}
		}
	}
	return true;
}

template <typename CharT>
template <typename cb_enter_t, typename cb_exit_t, typename cb_revisit_t,
	typename cb_ambig_t>
bool earley<CharT>::traverse_forest(const nidx_t &root, cb_enter_t cb_enter,
	cb_exit_t cb_exit, cb_revisit_t cb_revisit, cb_ambig_t cb_ambig)
{
	std::set<nidx_t> done;
	return _traverse_forest(root, done,
		cb_enter, cb_exit, cb_revisit, cb_ambig);
}


template <typename CharT>
template <typename cb_enter_t, typename cb_exit_t, typename cb_revisit_t,
	typename cb_ambig_t>
bool earley<CharT>::_traverse_forest(const nidx_t &root, std::set<nidx_t> &done,
	cb_enter_t cb_enter, cb_exit_t cb_exit, cb_revisit_t cb_revisit,
	cb_ambig_t cb_ambig)
{
	bool ret = true;
	std::set<std::vector<nidx_t>> pack;
	if (root.nt()) {
		auto it = pfgraph.find(root);
		if (it == pfgraph.end()) return false;
		pack = it->second;
	}
	cb_enter(root);
	done.insert(root);

	std::set<std::vector<nidx_t>> choosen_pack = pack.size() > 1
		? cb_ambig(root, pack) : pack; 
	for (auto &nodes: choosen_pack)
		for (auto &chd: nodes)
			if (!done.count(chd) || cb_revisit(chd)) 
				ret &= _traverse_forest(chd, done, cb_enter,
					cb_exit, cb_revisit, cb_ambig);
	cb_exit(root, choosen_pack);
	return ret;
}


template <typename CharT>
typename earley<CharT>::ptree_t earley<CharT>::get_parsed_tree() {
	nidx_t root(start, { 0, inputstr.length() });
	ptree_t pt;

	auto cb_enter = [](const nidx_t&){};
	auto cb_revisit = [](const auto&){ return false; };
	auto cb_exit = [&pt](const nidx_t& root,
		const std::set<std::vector<nidx_t>>& choice_set)
	{
		DBG( assert(choice_set.size() <= 1));
		if (root.nt()) pt.insert({root, choice_set});
	};
	auto cb_disambig_by_priority = [this](const nidx_t& root,
		const std::set<std::vector<nidx_t>>& ambset)
	{
		DBG(assert(root.nt()));
		int_t cur = -1, pchoice = INT32_MIN, maxp = INT32_MIN,
			pref_choice = INT32_MIN;

		for (auto & choice : ambset) {
			std::vector<lit> gprod;
			gprod.push_back(root.l);
			//get the production
			for( auto & nd : choice)
				gprod.emplace_back(nd.l);
			
			++cur;
			// find the top priority if any
			auto it = priority.find(gprod);
			if (it != priority.end() && it->second >= maxp)
				maxp = it->second, pchoice = cur;
			// find the preference if any
			if (prefer.count(gprod)) pref_choice = cur;
		}
		if (pchoice == INT32_MIN && pref_choice == INT32_MIN) {
			o::err() << "\n Could not resolve ambiguity,"
				" defaulting to first choice!\n";
			pchoice = 0;
		}
		std::set<std::vector<nidx_t>> choosen;
		auto it = std::next(ambset.begin(),
			int_t(pchoice >= 0 ? pchoice : pref_choice));
		choosen.insert(*it );
		return choosen;
	};

	traverse_forest(root, cb_enter, cb_exit, cb_revisit,
		cb_disambig_by_priority);
	return pt;
}

template <typename CharT>
uintmax_t earley<CharT>::count_parsed_trees() {
	nidx_t root(start, { 0, inputstr.length() });
	
	size_t count = 1;
	
	auto cb_enter = [](const auto&) {};
	auto cb_exit =  [](const auto&, const auto&) {};
	auto cb_keep_ambig = [&count](const nidx_t&, auto& ambset) {
		count *= ambset.size();
		return ambset;
	};
	auto cb_revisit =  [](const auto&) { return false; }; // revisit

	traverse_forest(root, cb_enter, cb_exit, cb_revisit, cb_keep_ambig);

	return count; 
}

template <typename CharT>
vector<typename earley<CharT>::arg_t> earley<CharT>::get_parse_graph_facts() {
	vector<arg_t> rts;
	auto rt_rel_output = [&rts] (string rel, size_t id,
		vector<variant<size_t, string>> args)
	{
		args.insert(args.begin(), { rel, id });
		rts.emplace_back(args);
	};
	iterate_forest(rt_rel_output);
	return rts;
}

template <typename CharT>
std::string earley<CharT>::to_tml_rule(const nidx_t nd) const {
	std::stringstream ss;
	if (nd.l.nt()) ss << to_stdstr(d.get(nd.l.n()));
	else if (nd.l.c() == (CharT) '\0') ss << "ε";
	else ss << to_stdstr(nd.l.c());
	ss << "(" << nd.span.first << " " << nd.span.second << ")";
	return ss.str();
}

template <typename CharT>
template <typename P>
bool earley<CharT>::to_tml_rule(ostream_t& ss, P &&pt) const{
	set<std::string> terminals;
	for (auto &it: pt.size()? pt : pfgraph ) {
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
std::string earley<CharT>::to_stdstr(const string& s) const {
	return to_string(to_string_t(s));
}

template <typename CharT>
std::string earley<CharT>::to_stdstr(const char32_t& ch) const {
	return to_string(to_string_t(ch));
}

template <typename CharT>
std::string earley<CharT>::dot_safe(const std::string &s) const {
	std::stringstream ss;
	for (size_t n = 0; n != s.size(); ++n) {
		if (s[n] == '"') ss << '\\';
		ss << s[n];
	}
	return ss.str();
}

template <typename CharT>
std::string earley<CharT>::grammar_text() const {
	std::stringstream txt;
	for (const auto &p : G) {
		txt << "\n\\l";
		size_t i = 0;
		for( const auto &l : p){
			if (l.nt()) txt << to_stdstr(d.get(l.n()));
			else if (l.c() != '\0') txt << to_stdstr(l.c());
			else txt << "ε";
			txt <<  " ";
			if (i++ == 0) txt << "-> ";
		}
	}
	return txt.str();
}

template <typename CharT>
template <typename P>
bool earley<CharT>::to_dot(ostream_t& ss, P &&pt) const {
	auto keyfun = [this] (const nidx_t & k){
		std::stringstream l;
		k.nt() ? l << to_stdstr(d.get(k.n()))
			: k.c() == '\0' ? l << "ε"
				: l << to_stdstr(k.c());
		l << "_" << k.span.first << "_" << k.span.second << "_";
		std::string desc = l.str();
		return std::pair<size_t, std::string>(
			std::hash<std::string>()(desc), desc);
	};
	ss << "digraph {\n";
	ss << "_input_" << "[label =\"" << dot_safe(to_stdstr(inputstr)) <<
		"\", shape = rectangle]" ;
	ss << "_grammar_" << "[label =\"" << dot_safe(grammar_text()) <<
		"\", shape = rectangle]" ;
	ss << "\nnode" << "[ ordering =\"out\"];";
	ss << "\ngraph" << "[ overlap =false, splines = true];";

	std::unordered_set<std::pair<size_t,size_t>, hasher_t> edgedone;
	edgedone.clear();
	for (auto &it: pt.size() ? pt : pfgraph) {
		auto key = keyfun(it.first);
		ss << "\n" << key.first << "[label=\"" << key.second <<"\"];";
		size_t p = 0;
		std::stringstream pstr;
		for (auto &pack : it.second) {
			pstr<<key.second<<p++;
			auto ambkey = std::hash<std::string>()(pstr.str());
			ss << "\n" << ambkey << "[shape = point,label=\"" <<
				pstr.str() << "\"];";
			if (edgedone.insert({ key.first, ambkey }).second)
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

// collects all possible variations of the given item's rhs while respecting the
// span of the item and stores them in the set ambset. 
template <typename CharT>
void earley<CharT>::sbl_chd_forest(const item &eitem,
	std::vector<nidx_t> &curchd, size_t xfrom,
	std::set<std::vector<nidx_t>> &ambset)
{
	//check if we have reached the end of the rhs of prod
	if (G[eitem.prod].size() <= curchd.size() + 1)  {
		// match the end of the span we are searching in.
		if (curchd.back().span.second == eitem.set)
			ambset.insert(curchd);
		return;
	}
	// curchd.size() refers to index of cur literal to process in the rhs of production
	nidx_t nxtl = G[eitem.prod][curchd.size() + 1];
	// set the span start/end of the terminal symbol 
	if (!nxtl.nt()) {
		nxtl.span.first = xfrom;
		// for empty, use same span edge as from
		if (nxtl.c() == (CharT) '\0') nxtl.span.second = xfrom;
		// ensure well-formed combination (matching input) early
		else if (xfrom < inputstr.size() &&
					inputstr.at(xfrom) == nxtl.c())  
			nxtl.span.second = ++xfrom ;
		else // if not building the correction variation, prune this path quickly 
			return;
		// build from the next in the line
		size_t lastpos = curchd.size();
		curchd.push_back(nxtl),
		sbl_chd_forest(eitem, curchd, xfrom, ambset);
		curchd.erase(curchd.begin() + lastpos, curchd.end());
	} else {
		// get the from/to span of all non-terminals in the rhs of production.
		nxtl.span.first = xfrom;
		
		//auto &nxtl_froms = sorted_citem[nxtl.n()][xfrom];
		auto &nxtl_froms = sorted_citem[{nxtl.n(),xfrom}];
		for (auto &v : nxtl_froms) {
			// ignore beyond the span
			if (v.set > eitem.set) continue;
			// store current and recursively build for next nt
			size_t lastpos = curchd.size(); 
			nxtl.span.second = v.set,
			curchd.push_back(nxtl), xfrom = v.set,
			sbl_chd_forest(eitem, curchd, xfrom, ambset);
			curchd.erase(curchd.begin() + lastpos, curchd.end());
		}
	}
}
template <typename CharT>
void earley<CharT>::pre_process(const item &i){

	//sorted_citem[G[i.prod][0].n()][i.from].emplace_back(i);
	if (completed(i))
		sorted_citem[{ G[i.prod][0].n(), i.from }].emplace_back(i),
		rsorted_citem[{ G[i.prod][0].n(), i.set }].emplace_back(i);
	else if (bin_lr) {
		// Precreating temporaries to help in binarisation later
		// each temporary represents a partial rhs production with
		// atleast 3 symbols
		if (i.dot >= 3) {
			std::vector<lit> v(G[i.prod].begin() + 1,
						G[i.prod].begin() + i.dot);
			lit tlit;
			if (bin_tnt.find(v) == bin_tnt.end()) {
				stringstream ss;
				put(ss << "temp", tid++);
				tlit = lit{ d.get(ss.str()) };
				bin_tnt.insert({ v, tlit });
			}
			else tlit = bin_tnt[v];
			
			//DBG(print(o::dbg(), i);)
			//o::dbg()<< endl << d.get(tlit.n()) << v << endl;
			sorted_citem[{ tlit.n(), i.from }].emplace_back(i),
			rsorted_citem[{ tlit.n(), i.set }].emplace_back(i);
		}
	}
}
template <typename CharT>
bool earley<CharT>::forest() {
	bool ret = false;
	// clear forest structure if any
	pfgraph.clear();
	bin_tnt.clear();
	tid = 0;
	// set the start root node
	size_t len = inputstr.length();
	nidx_t root(start, {0,len});
	// preprocess earley items for faster retrieval
	emeasure_time_start(tspfo, tepfo);
	int count = 0;

	for(size_t n=0; n<len+1 ; n++)
		for (const item& i : S[n]) {
			count++;
			pre_process(i);
		}

	emeasure_time_end(tspfo, tepfo) << " :: preprocess time ," <<
						"size : "<< count << "\n";
	o::inf() <<"sort sizes : " << sorted_citem.size() << " " <<
						rsorted_citem.size() <<" \n";
	// build forest
	emeasure_time_start(tsf, tef);
	ret = bin_lr ? build_forest2(root) : build_forest(root);
	emeasure_time_end(tsf, tef) <<" :: forest time "<<endl ;

	o::pms() <<"# parse trees " << count_parsed_trees() <<endl;
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
bool earley<CharT>::bin_lr_comb(const item& eitem,
	std::set<std::vector<nidx_t>>& ambset)
{
	std::vector<nidx_t> rcomb, lcomb;
	if (eitem.dot < 2) return false;

	nidx_t right = G[eitem.prod][eitem.dot-1];

	if (!right.nt()) {
		right.span.second = eitem.set;
		if (right.c() == (CharT) '\0')
			right.span.first = right.span.second;
		else if (inputstr.at(eitem.set -1) == right.c() )
			right.span.first = eitem.set -1 ;
		else return false;
		rcomb.emplace_back(right);
	} else {
		auto &rightit = rsorted_citem[{right.n(), eitem.set}];
		for (auto &it : rightit)
			if (eitem.from <= it.from) 
				right.span.second = it.set,
				right.span.first = it.from,
				rcomb.emplace_back(right);
	}
	// many literals in rhs
	if (eitem.dot > 3) {
		//DBG(print(o::dbg(), eitem);)
		std::vector<lit> v(G[eitem.prod].begin() + 1,
					G[eitem.prod].begin() + eitem.dot - 1);
		DBG(assert( bin_tnt.find(v) != bin_tnt.end());)
		nidx_t left = bin_tnt[v];
		//DBG(COUT << std::endl << d.get(bin_tnt[v].n()) << std::endl);
		auto &leftit = sorted_citem[{left.n(), eitem.from}];
		// doing left right optimization
		for (auto &it : leftit) 
			for (auto &rit : rcomb)    
				if (it.set == rit.span.first) {
					left.span.first = it.from;
					left.span.second = it.set;
					ambset.insert({left, rit});
				} 
	}
	// exact two literals in rhs
	else if (eitem.dot == 3) {
		nidx_t left = G[eitem.prod][eitem.dot-2];
		if (!left.nt()) {
			left.span.first = eitem.from;
			if (left.c() == (CharT) '\0')
				left.span.second = left.span.first;
			else if (inputstr.at(eitem.from) == left.c() )
				left.span.second = eitem.from + 1  ;
			else return false;
			//do Left right optimisation
			for (auto &rit : rcomb)  
				if (left.span.second == rit.span.first)
					ambset.insert({ left, rit });
		}
		else {
			auto &leftit = sorted_citem[{left.n(), eitem.from}];
			for (auto &it : leftit) 
				for (auto &rit : rcomb)    
					if (it.set == rit.span.first)
						left.span.first = it.from,
						left.span.second = it.set,
						ambset.insert({ left, rit });
		}
	}
	else {
		DBG(assert(eitem.dot == 2));
		for (auto &rit : rcomb)
			if (eitem.from <= rit.span.first)
				ambset.insert({ rit });
	}
	return true;
}

// builds the forest starting with root
template <typename CharT>
bool earley<CharT>::build_forest ( const nidx_t &root ) {
	if (!root.nt()) return false;
	if (pfgraph.find(root) != pfgraph.end()) return false;

	//auto &nxtset = sorted_citem[root.n()][root.span.first];
	auto &nxtset = sorted_citem[{root.n(),root.span.first}];
	std::set<std::vector<nidx_t>> ambset;
	for (const item &cur : nxtset) {
		if (cur.set != root.span.second) continue;
		assert(root.n() == G[cur.prod][0].n() );
		nidx_t cnode( G[cur.prod][0], {cur.from, cur.set} );
		vector<nidx_t> nxtlits;
		sbl_chd_forest(cur, nxtlits, cur.from, ambset );
		pfgraph[cnode] = ambset;
		for (auto &aset : ambset)
			for (const nidx_t& nxt : aset) {
				build_forest(nxt);
			}
	}	
	return true;
}

template <typename CharT>
bool earley<CharT>::build_forest2 (const nidx_t &root) {
	if (!root.nt()) return false;
	if (pfgraph.find(root) != pfgraph.end()) return false;

	//auto &nxtset = sorted_citem[root.n()][root.span.first];
	auto &nxtset = sorted_citem[{ root.n(),root.span.first }];
	std::set<std::vector<nidx_t>> ambset;
	for (const item &cur: nxtset) {
		if (cur.set != root.span.second) continue;
		nidx_t cnode(completed(cur) ? G[cur.prod][0] : lit{ root.n() },
			{ cur.from, cur.set } );
		bin_lr_comb(cur, ambset);
		pfgraph[cnode] = ambset;
		for (auto &aset: ambset )
			for (const nidx_t& nxt : aset) {
				build_forest2(nxt);
			}
	}
	return true;
}

template <typename CharT>
vector<typename earley<CharT>::node_children> earley<CharT>::get_children(
	const nidx_t nd, bool all) const
{
	vector<node_children> ncs;
	auto label = [this](const nidx_t p, bool all=1) {
		return p.nt() ? d.get(p.n()) : (all ? string{p.c()} : string{});
	};
	auto it = pfgraph.find(nd);
	if (it == pfgraph.end()) return {{}};
	bool amb = false;
	if (print_ambiguity && it->second.size() > 1) amb = true, o::inf() <<"'"
		<< to_stdstr(label(nd, true)) <<"' is ambiguous\n";
	size_t c = 0;
	for (auto &pack : it->second) {
		if (amb) o::inf() << "\tpack " << ++c << ":\t";
		ncs.emplace_back();
		for (auto& p : pack) {
			if (amb) o::inf() << "\t'" <<
				to_stdstr(label(p, true)) << "' ";
			ncs.back().push_back(
				pair<string, const nidx_t>(label(p, all), p));
		}
		if (amb) o::inf() << "\n";
	}
	return ncs;
}

template <typename CharT>
typename earley<CharT>::string earley<CharT>::shorten(const string& s,
	size_t len, const string& suffix) const
{
	if (s.size() > len) return s.substr(0, len) + suffix;
	return s;
}

template <typename CharT>
typename earley<CharT>::string earley<CharT>::flatten(const nidx_t p) const {
	stringstream ss;
	auto it = pfgraph.find(p);
	if (it == pfgraph.end()) return {{}};
	for (auto &pack : it->second) {
		for (auto &p : pack)
			if (p.nt()) {
				auto flat = flatten(p);
				if (flat.size() && flat[0] != 0 &&
					flat[0] != char_traits<CharT>::eof())
						put(ss, flat);
			} else put(ss, p.c());
		break; // traverse only the first pack of each node
	}
	return ss.str();
}

template <typename CharT>
void earley<CharT>::down(const nidx_t& p, const actions& a) const {
	auto label = p.is_builtin() ? d.get(p.builtin())
		: p.nt() ? d.get(p.n()) : string{ p.c() };
	auto print_traversing_info = [&label, &p, this]() {
		std::string wrap = p.nt() ? "" : "'";
		std::string l = to_stdstr(label);
		bool print_flattened = true;
		if (l.size() == 1 && !isprint(l[0])) {
			print_flattened = false;
			if (l[0] == 0) l = "ε";
			else {
				std::stringstream ss;
				ss << "\\" << (size_t) l[0];
				l = ss.str();
			}
		}
		o::inf() << "down(" << wrap << l << wrap << ")";
		if (print_flattened) l = to_stdstr(shorten(flatten(p))),
			(!l.size() || l[0] == 0) ? o::inf()
				: o::inf() << ": \t\"" << l << "\"";
		o::inf() << "\n";		
	};
	if (print_traversing) print_traversing_info();
	// include also ebnf-transformation generated nodes
	if (label.size() > 1 && label[0]==(CharT)'_' && label[1]==(CharT)'R')
		label = label.substr(2, label.find_last_of((CharT)'_') - 2);
	auto it = a.find(label);
	if (it != a.end()) it->second(p, get_children(p));
	else if (auto_passthrough) down(get_children(p), a);
}

template <typename CharT>
void earley<CharT>::topdown(const string& start, const actions& a) const {
	auto it = pfgraph.begin();
	for ( ; it != pfgraph.end() &&
		!(it->first.nt() && d.get(it->first.n()) == start); ++it) ;
	if (it != pfgraph.end()) down(it->first, a);
}

template <>
std::basic_string<char> earley<char>::epsilon()         const { return  "ε"; }
template <>
std::basic_string<char32_t> earley<char32_t>::epsilon() const { return U"ε"; }

template bool earley<char>::to_tml_facts(ostream_t& os, ptree_t&& p) const;
template bool earley<char32_t>::to_tml_facts(ostream_t& os, ptree_t&& p) const;
template bool earley<char>::to_tml_rule(ostream_t& os, ptree_t&& p) const;
template bool earley<char32_t>::to_tml_rule(ostream_t& os, ptree_t&& p) const;
template bool earley<char>::to_dot(ostream_t& os, ptree_t&& p) const;
template bool earley<char32_t>::to_dot(ostream_t& os, ptree_t&& p) const;

template class earley<char>;
template class earley<char32_t>;
