#include <vector>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <list>
#include <string>
#include <variant>
#include <cassert>
#include <iostream>
#include <sstream>
#include <fstream>
#include <functional>
#include <cstdint>
#include "input.h"

#ifdef DEBUG
#define DBG(x) x
#else
#define DBG(x)
#endif

#define tdiff(start, end) ((double(end - start) / CLOCKS_PER_SEC) * 1000)
#define emeasure_time_start(start, end) clock_t end, start = clock()
#define emeasure_time_end(start, end) end = clock(), o::pms() << std::fixed << \
	std::setprecision(2) << tdiff(start, end) << " ms"

std::basic_ostream<char32_t>& operator<<(std::basic_ostream<char32_t>& os,
	const std::string& s);

std::basic_ostream<char32_t>& operator<<(std::basic_ostream<char32_t>& os,
	const char* s);

template <typename CharT>
class earley {
public:
	typedef std::basic_stringstream<CharT> stringstream;
	typedef std::basic_ostream<CharT> ostream;
	typedef std::basic_string<CharT> string;
	typedef std::vector<string> strings;
	typedef std::vector<std::pair<string,
			std::vector<std::vector<string>>>> grammar;
	typedef std::variant<size_t, CharT> lit_t;
	typedef std::function<bool(CharT)> char_builtin_t;
	typedef std::map<string, char_builtin_t> char_builtins_map;
	bool print_ambiguity  = false;
	bool print_traversing = false;
	bool auto_passthrough = true;
private:
	struct lit : public lit_t {
		using typename lit_t::variant;
		bool nt() const { return std::holds_alternative<size_t>(*this);}
		size_t n() const { return std::get<size_t>(*this); }
		CharT c() const { return std::get<CharT>(*this); }
		int_t builtin = -1;
		bool is_builtin() const { return builtin != -1; }
	};
	string to_str(const lit& l) const {
		if (l.is_builtin()) return d.get(l.builtin);
		else if (l.nt()) return d.get(l.n());
		else if (l.c() == (CharT) '\0') return epsilon();
		else return string{ '\'', l.c(), '\'' };
	}
	string to_str(const string_t& s) const;
	struct pnode {
		lit l;
		std::pair<size_t, size_t> span; // start/end of the matched span
		pnode(const lit _l, const std::pair<size_t, size_t> _span={0,0})
			: l(_l), span(_span) {}
		bool nt() const { return l.nt(); }
		size_t n() const { return l.n(); }
		CharT c() const { return l.c(); }
		bool is_builtin() const { return l.is_builtin(); }
		int_t builtin() const { return l.builtin; }
		bool operator<(const pnode& i) const {
			if (l != i.l) return l < i.l;
			if (span != i.span) return span < i.span;
			return false;
		}
		bool operator==(const pnode& rhs) const {
			if (l == rhs.l && span == rhs.span ) return true;
			else return false;
		}
	};

	DBG(template <typename CharU> friend ostream_t& operator<<(
		ostream_t& os, const typename earley<CharU>::lit& l);)
	DBG(template <typename CharU> friend ostream_t& operator<<(
		ostream_t& os,
		const std::vector<typename earley<CharU>::lit>& v);)
	std::vector<std::vector<lit>> G;
	std::map<std::vector<lit>, int_t> priority;
	std::set<std::vector<lit>> prefer;
	lit start;
	std::map<lit, std::set<size_t>> nts;
	std::set<size_t> nullables;
	string inputstr;
	struct item {
		item(size_t set, size_t prod, size_t from, size_t dot) :
			set(set), prod(prod), from(from), dot(dot) {}
		size_t set, prod, from, dot;
		// mutable std::set<item> advancers, completers;
		bool operator<(const item& i) const {
			if (set != i.set) return set < i.set;
			if (prod != i.prod) return prod < i.prod;
			if (from != i.from) return from < i.from;
			return dot < i.dot;
		}
		bool operator==(const item& i) const {
			if (set != i.set || prod != i.prod ||
				from != i.from || dot != i.dot)
					return false;
			return true;
		}
	};

	lit get_lit(const item& i) const { return G[i.prod][i.dot]; }
	bool completed(const item& i) const { return G[i.prod].size()==i.dot; }
	lit get_nt(const item& i) const { return G[i.prod][0]; }
	bool all_nulls(const std::vector<lit>& p) const;
	ostream& print(ostream& os, const item& i) const;
	void scan(const item& i, size_t n, CharT ch);
	void scan_builtin(const item& i, size_t n, const string& s);
	bool nullable(const item& i) const {
		return i.dot < G[i.prod].size() &&
			((get_lit(i).nt() &&
			nullables.find(get_lit(i).n()) !=
			nullables.end()) ||
			(!get_lit(i).nt() && get_lit(i).c() == '\0'));
	}

	struct {
		std::map<string, size_t> m;
		std::vector<string> v;
		size_t get(const string& s) {
			if (auto it = m.find(s); it != m.end())
				return it->second;
			return m.emplace(s, v.size()), v.push_back(s),
			       v.size() - 1;
		}
		string get(size_t n) const { return v[n]; }
	} d;
	
public:
	typedef std::map<item, std::set<std::vector<item>>> item_forest_t;
	
	typedef pnode nidx_t;
	typedef std::map<nidx_t, std::set<std::vector<nidx_t>>> parse_forest_t;
	typedef parse_forest_t ptree_t;
	typedef std::vector<std::variant<size_t, string>> arg_t;
	typedef std::vector<std::pair<string, const nidx_t>> node_children;
	typedef std::vector<node_children> node_children_variations;
	typedef std::function<void(const nidx_t&,
		const node_children_variations&)> action_fn;
	typedef std::pair<string, action_fn> action_pair;
	typedef std::map<string, action_fn> actions;
	earley(const grammar& g, const char_builtins_map& bm = {},
		bool _bin_lr = false, bool _incr_gen_forest = false);
	earley(const grammar& g, bool _bin_lr = false,
		bool _incr_gen_forest = false) :
			earley(g, {}, _bin_lr, _incr_gen_forest) {}
	earley(const std::vector<production>& g, const char_builtins_map& bm,
		bool _bin_lr = false, bool _incr_gen_forest = false);
	earley(const std::vector<production>& g, bool _bin_lr = false, 
		bool _incr_gen_forest = false) :
			earley(g, {}, _bin_lr, _incr_gen_forest) {}

	bool recognize(const string s);
	std::vector<arg_t> get_parse_graph_facts();
	string flatten(string label, const nidx_t nd) const;
	uintmax_t count_parsed_trees() ;
	ptree_t get_parsed_tree();

	template <typename cb_enter_t, typename cb_exit_t,
		typename cb_revisit_t, typename cb_ambig_t>
	bool traverse_forest(const nidx_t &root, cb_enter_t cb_enter, 
		cb_exit_t cb_exit, cb_revisit_t cb_revisit,cb_ambig_t cb_ambig);
	void topdown(const string& start, const actions& a) const;
	void down(const nidx_t& nd, const actions& a) const;
	void down(const node_children& nc, const actions& a) const {
		for (auto&c : nc) down(c.second, a);	
	};
	void down(const node_children_variations& ncs, const actions& a) const {
		for (auto&nc : ncs) down(nc, a);
	};
	string shorten(const string& s, size_t len = 60,
		const string& suffix = string{ '.', '.', '.' }) const;
	string flatten(const nidx_t nd) const;
	ptree_t get_parsed_tree(size_t);
	size_t count_parsed_trees() const;
private:
	template <typename cb_enter_t, typename cb_exit_t,
		typename cb_revisit_t, typename cb_ambig_t>
	bool _traverse_forest(const nidx_t &root, std::set<nidx_t> &done,
		cb_enter_t cb_enter, cb_exit_t cb_exit, cb_revisit_t cb_revisit,
		cb_ambig_t cb_ambig);
	string epsilon() const;
	node_children_variations get_children(const nidx_t nd, bool all = false)
		const;
	bool bin_lr;  //enables binarizaion and left right optimization
	bool incr_gen_forest; //enables incremental generation of forest
	ostream& put(ostream& os, const size_t& n) const {
		for (const auto& ch : to_string_(n)) os.put((CharT) ch);
		return os;
	}
	ostream& put(ostream& os, const CharT& ch) const {
		return os.put(ch); }
	ostream& put(ostream& os, const string& s) const {
		for (const auto& ch : s) os.put(ch);
		return os;
	}
	template<typename P=ptree_t>
	bool to_dot(ostream_t& os, P && p = ptree_t()) const;
	std::string dot_safe(const std::string& s) const;
	std::string to_stdstr(const string& s) const;
	std::string to_stdstr(const char32_t& s) const;
	struct hasher_t{
		size_t hash_size_t(const size_t &val) const{
			return std::hash<size_t>()(val) + 0x9e3779b9 +
							(val << 6) + (val >> 2);
		}
		size_t operator()(const std::pair<size_t, size_t> &k) const {
			// lets substitute with better if possible.
			std::size_t h = 0;
			h ^= hash_size_t(k.first); 
			h ^= hash_size_t(k.second);
			return h;
		}
		size_t operator()(const nidx_t &k) const {
			// lets substitute with better if possible.
			std::size_t h = 0;
			h ^= hash_size_t(k.span.first); 
			h ^= hash_size_t(k.span.second);
			h ^= hash_size_t(size_t(k.l.nt()?k.l.n():k.c()));
			return h;
		}
		size_t operator()(const item &k) const {
			// lets substitute with better if possible.
			std::size_t h = 0;
			h ^= hash_size_t(k.set);
			h ^= hash_size_t(k.from);
			h ^= hash_size_t(k.prod);
			h ^= hash_size_t(k.dot);
			return h;
		}
	};
	//std::unordered_map< size_t, 
	//	std::unordered_map<size_t, std::vector<item>>>  sorted_citem;
	std::unordered_map<std::pair<size_t, size_t>, std::vector<item>,
		hasher_t> sorted_citem, rsorted_citem;
	parse_forest_t pfgraph;
	std::map<std::vector<earley::lit>, earley::lit> bin_tnt; // binariesed temporary intermediate non-terminals
	size_t tid; // id for temporary non-terminals
	std::vector<char_builtin_t> builtins;
	std::vector<std::map<CharT, size_t>> builtin_char_prod; // char -> prod
	std::string grammar_text() const;
	bool build_forest ( const nidx_t &root );
	bool build_forest2 ( const nidx_t &root );
	void pre_process(const item &i);
	bool forest();
	bool bin_lr_comb(const item&, std::set<std::vector<nidx_t>>&);
	void sbl_chd_forest(const item&, std::vector<nidx_t>&, size_t,
		std::set<std::vector<nidx_t>>&);
	template <typename T, typename P = ptree_t>
	bool iterate_forest(T, P &&pt = ptree_t()) const;
	//bool visit_forest(std::function<void(std::string, size_t, std::vector<std::variant<size_t, std::string>>)> out_rel) const;
	uintmax_t _count_parsed_trees(const nidx_t &,
		std::unordered_set<nidx_t, hasher_t>&) const;
	// only store graph as facts
	template<typename P = ptree_t>
	bool to_tml_facts(ostream_t& os, P && p = ptree_t()) const;
	//make parse forest grammar
	template<typename P = ptree_t>
	bool to_tml_rule(ostream_t& os, P && p = ptree_t()) const;
	std::string to_tml_rule(const nidx_t nd) const;
	template <typename CharU>
	friend int test_out(int c, earley<CharU> &e);
	typedef std::unordered_set<earley<CharT>::item, earley<CharT>::hasher_t> container_t;
	typedef container_t::iterator container_iter;
	std::vector<container_t> S;
	container_iter add(container_t& t, const item& i);
	void complete(const item& i, container_t& t);
	void predict(const item& i, container_t& t);


	struct overlay_tree {
		std::vector<int> choices;
		nidx_t &root;
		earley::parse_forest_t &pf;
		overlay_tree(nidx_t &_r, earley::parse_forest_t &_pf):
		root(_r), pf(_pf){};
	};
};
