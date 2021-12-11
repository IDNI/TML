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
#define DEBUG

#ifdef DEBUG
#define DBG(x) x
#else
#define DBG(x)
#endif
typedef char char_t;

class earley {
	struct lit : public std::variant<size_t, char> {
		using std::variant<size_t, char>::variant;
		bool nt() const { return std::holds_alternative<size_t>(*this); }
		size_t n() const { return std::get<size_t>(*this); }
		char c() const { return std::get<char>(*this); }
		size_t st = 0;  // start of span match
		size_t en = 0;	// end of span match
		bool operator<(const lit& i) const {
			if(std::variant<size_t, char>(*this) != std::variant<size_t, char>(i) )
			 	return std::variant<size_t, char>(*this) < std::variant<size_t, char>(i);
			if(st != i.st) return st < i.st;
			if (en != i.en) return en < i.en;
			return false;
		}
	};
	DBG(friend std::ostream& operator<<(std::ostream& os, const lit& l);)
	DBG(friend std::ostream& operator<<(std::ostream& os,
		const std::vector<lit>& v);)
	std::vector<std::vector<lit>> G;
	lit start;
	std::map<lit, std::set<size_t>> nts;
	std::set<size_t> nullables;
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
	earley(const std::vector<
		std::pair<
			std::string,
			std::vector<std::vector<std::string>>>>& g);
	bool recognize(const char_t* s);

	typedef lit nidx_t;
	bool to_dot();
	std::set<item> citem;
	std::map<nidx_t, std::set<std::vector<nidx_t>>> pfgraph;
	const std::vector<item> find_all( size_t xfrom, size_t nt, int end = -1  );
	bool forest(std::vector<item> const&);
	void sbl_chd_forest(const item &chd, std::vector<nidx_t>& , size_t xfrom, std::set<std::vector<nidx_t>>&);
};
