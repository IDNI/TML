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
private:
	struct lit : public lit_t {
		using lit_t::variant;
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
			if(l != i.l )	return l < i.l;
			if(span != i.span ) return span < i.span;
			return false;
		}
		bool operator==(const pnode& rhs) const {
			if(l == rhs.l && span == rhs.span ) return true;
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
	typename std::set<item>::iterator add(std::set<item>& t, const item& i);
	void complete(const item& i, std::set<item>& t);
	void predict(const item& i, std::set<item>& t);
	void scan(const item& i, size_t n, CharT ch);
	void scan_builtin(const item& i, size_t n, CharT ch);
	bool nullable(const item& i) const {
		return	i.dot < G[i.prod].size() &&
			((get_lit(i).nt() &&
			nullables.find(get_lit(i).n()) !=
			nullables.end()) ||
			(!get_lit(i).nt() && get_lit(i).c() == '\0'));
	}
	std::set<item> S;

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
	typedef pnode nidx_t;
	typedef std::map<nidx_t, std::set<std::vector<nidx_t>>> parse_forest_t;
	typedef parse_forest_t ptree_t;
	typedef std::vector<std::variant<size_t, string>> arg_t;
	typedef std::vector<std::pair<string, const nidx_t>> node_children;
	earley(const grammar& g, const char_builtins_map& bm,
		bool _bin_lr = false);
	earley(const grammar& g, bool _bin_lr) : earley(g, {}, _bin_lr) {}
	earley(const grammar& g)               : earley(g, {}) {}
	earley(const std::vector<production>& g, const char_builtins_map& bm,
		bool _bin_lr = false);
	earley(const std::vector<production>& g, bool _bin_lr) :
		earley(g, {}, _bin_lr) {}
	earley(const std::vector<production>& g) : earley(g, {}) {}
	bool recognize(const string s);
	std::vector<arg_t> get_parse_graph_facts();
	string flatten(string label, const nidx_t nd) const;
	uintmax_t count_parsed_trees() ;
	ptree_t get_parsed_tree();

	template <typename cb_enter_t , 
				typename cb_exit_t
				,typename cb_revisit_t, 
				typename cb_ambig_t 
				>
	bool traverse_forest( const nidx_t &root, 
	cb_enter_t cb_enter, 
	cb_exit_t cb_exit, 
	cb_revisit_t cb_revisit,
	cb_ambig_t cb_ambig 
	);
private:
	template <typename cb_enter_t, 
				typename cb_exit_t,
				typename cb_revisit_t,
				typename cb_ambig_t
				>
	bool _traverse_forest( const nidx_t &root, 
				std::set<nidx_t> &done,
				cb_enter_t cb_enter, 
				cb_exit_t cb_exit, 
				cb_revisit_t cb_revisit,
				cb_ambig_t cb_ambig 
				);
	string epsilon() const;
	node_children get_children(const nidx_t nd, bool all) const;
	bool bin_lr;  //enables binarizaion and left right optimization
	template<typename P=ptree_t>
	bool to_dot(ostream_t& os, P && p = ptree_t());
	std::string to_dot_safestring(const string& s) const;
	struct hasher_t{
		size_t hash_size_t(const size_t &val) const{
			return std::hash<size_t>()(val)  + 0x9e3779b9 + (val << 6) + (val >> 2);
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
	};
	//std::unordered_map< size_t, 
	//	std::unordered_map<size_t, std::vector<item>>>  sorted_citem;
	std::unordered_map< std::pair<size_t,size_t> , std::vector<item>, hasher_t >  
		sorted_citem, rsorted_citem;
	parse_forest_t pfgraph;
	std::map<std::vector<earley::lit>, earley::lit> bin_tnt; // binariesed temporary intermediate non-terminals
	std::vector<char_builtin_t> builtins;
	std::vector<std::map<CharT, size_t>> builtin_char_prod; // char -> prod
	std::string grammar_text();
	bool build_forest ( const nidx_t &root );
	bool build_forest2 ( const nidx_t &root );
	bool forest();
	bool bin_lr_comb(const item&, std::set<std::vector<nidx_t>>&);
	void sbl_chd_forest(const item&, std::vector<nidx_t>&, size_t,
		std::set<std::vector<nidx_t>>&);
	template <typename T, typename P = ptree_t>
	bool iterate_forest(T, P &&pt = ptree_t()) const;
	//bool visit_forest(std::function<void(std::string, size_t, std::vector<std::variant<size_t, std::string>>)> out_rel) const;
	uintmax_t _count_parsed_trees(const nidx_t &, std::unordered_set<nidx_t, hasher_t>&) const;
	// only store graph as facts
	template<typename P = ptree_t>
	bool to_tml_facts(ostream_t& os, P && p = ptree_t()) const;
	//make parse forest grammar
	template<typename P = ptree_t>
	bool to_tml_rule(ostream_t& os, P && p = ptree_t()) const;
	std::string to_tml_rule(const nidx_t nd) const;
	template <typename CharU>
	friend int test_out(int c, earley<CharU> &e);

	struct overlay_tree {
		std::vector<int> choices;
		nidx_t &root;
		earley::parse_forest_t &pf;
		
		overlay_tree(nidx_t &_r, earley::parse_forest_t &_pf):
		root(_r), pf(_pf){};
	};
};
