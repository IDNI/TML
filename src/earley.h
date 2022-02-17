#include <vector>
#include <map>
#include <set>
#include <unordered_map>
#include <list>
#include <string>
#include <variant>
#include <cstring>
#include <cassert>
#include <iostream>
#include <sstream>
#include <fstream>
#include <functional>
#include "input.h"

#ifdef DEBUG
#define DBG(x) x
#else
#define DBG(x)
#endif
//typedef char char_t;

#define tdiff(start, end) ((double(end - start) / CLOCKS_PER_SEC) * 1000)
#define emeasure_time_start(start, end) clock_t end, start = clock()
#define emeasure_time_end(start, end) end = clock(), o::pms() << std::fixed << \
	std::setprecision(2) << tdiff(start, end) << " ms"
class earley {
	struct lit : public std::variant<size_t, char> {
		using std::variant<size_t, char>::variant;
		bool nt() const { return std::holds_alternative<size_t>(*this);}
		size_t n() const { return std::get<size_t>(*this); }
		char c() const { return std::get<char>(*this); }
	};

	struct pnode {
		earley::lit l;
		std::pair<size_t, size_t> span; // start/end of the matched span
		pnode(const earley::lit _l,
			const std::pair<size_t, size_t> _span = {0, 0} ): 
		l(_l),span(_span){}
		
		bool nt() const { return l.nt(); }
		size_t n() const { return l.n(); }
		char c() const { return l.c(); }
		
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

	DBG(friend std::ostream& operator<<(std::ostream& os, const lit& l);)
	DBG(friend std::ostream& operator<<(std::ostream& os,
		const std::vector<lit>& v);)
	std::vector<std::vector<lit>> G;
	lit start;
	std::map<lit, std::set<size_t>> nts;
	std::set<size_t> nullables;
	std::string inputstr;
	struct item {
		item(size_t set, size_t prod, size_t from, size_t dot) :
			set(set), prod(prod), from(from), dot(dot) {}
		size_t set, prod, from, dot;
		mutable std::set<item> advancers, completers;
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
	
/*	struct ast {
		ast() {}
		ast(const item& i) : i(i) {}
		item i;
		std::set<std::vector<ast*>> next;
	};*/
	lit get_lit(const item& i) const { return G[i.prod][i.dot]; }
	bool completed(const item& i) const { return G[i.prod].size()==i.dot; }
	lit get_nt(const item& i) const { return G[i.prod][0]; }
	bool all_nulls(const std::vector<lit>& p) const;
	std::ostream& print(std::ostream& os, const item& i) const;
	std::set<item>::iterator add(std::set<item>& t, const item& i);
	void complete(const item& i, std::set<item>& t);
	void predict(const item& i, std::set<item>& t);
	void scan(const item& i, size_t n, char ch);
	bool nullable(const item& i) const {
		return	i.dot < G[i.prod].size() &&
			((get_lit(i).nt() &&
			nullables.find(get_lit(i).n()) !=
			nullables.end()) ||
			(!get_lit(i).nt() && get_lit(i).c() == '\0'));
	}
	std::set<std::string> init_char_builtins();
	std::set<item> S;

	struct {
		std::map<std::string, size_t> m;
		std::vector<std::string> v;
		size_t get(const std::string& s) {
			if (auto it = m.find(s); it != m.end())
				return it->second;
			return m.emplace(s, v.size()), v.push_back(s),
			       v.size() - 1;
		}
		std::string get(size_t n) const { return v[n]; }
	} d;
public:
	typedef pnode nidx_t;
	typedef std::vector<std::variant<size_t, std::string>> arg_t;
	typedef std::vector<std::pair<std::string, const nidx_t>> node_children;
	earley(const std::vector<
		std::pair<
			std::string,
			std::vector<std::vector<std::string>>>>& g);
	earley(const std::vector<production>& g);
	bool recognize(const char* s);
	std::vector<arg_t> get_parse_graph_facts();
	raw_progs get_raw_progs(dict_t* dict);
private:
	bool to_dot(ostream_t& os);
	std::string to_dot_safestring(const std::string& s) const;
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
	std::unordered_map< std::pair<size_t,size_t> , std::vector<item>, hasher_t >  sorted_citem;
	std::map<nidx_t, std::set<std::vector<nidx_t>>> pfgraph;
	std::string grammar_text();
	bool forest(const nidx_t & );
	void sbl_chd_forest(const item&, std::vector<nidx_t>&, size_t,
		std::set<std::vector<nidx_t>>&);
	template<typename T>
	bool visit_forest(T) const;
	//bool visit_forest(std::function<void(std::string, size_t, std::vector<std::variant<size_t, std::string>>)> out_rel) const;
	
	// only store graph as facts
	bool to_tml_facts(ostream_t& os) const;
	//make parse forest grammar
	bool to_tml_rule(ostream_t& os) const;
	std::string to_tml_rule(const nidx_t nd) const;
	friend int test_out(int c, earley &e);
	// following is used by get_raw_progs()
	dict_t* dict;
	node_children get_children(const nidx_t nd, bool all) const;
	std::string flatten(std::string label, const nidx_t nd);
	raw_term pred_to_raw_term(const nidx_t nd);
	raw_term to_raw_term(const nidx_t nd);
	raw_prog to_raw_prog(const nidx_t nd);
	void preds_to_raw_rule(raw_rule &rr, bool head, const nidx_t p);
	void args_to_raw_term(raw_term& rt, const nidx_t p);
	void elem_to_raw_term(raw_term& rt, const nidx_t p);
	void add_fact(raw_prog &rp, const nidx_t p);
	void add_rule(raw_prog &rp, const nidx_t p);
	void add_statements(raw_prog &rp, const nidx_t p);
};
