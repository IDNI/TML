#include "lp.h"
#include "input.h"

struct dictcmp {
	bool operator()(const std::pair<cws, size_t>& x,
			const std::pair<cws, size_t>& y) const {
		return	x.second != y.second ? x.second < y.second :
			wcsncmp(x.first, y.first, x.second) < 0;
	}
};

class driver {
	std::map<std::pair<cws, size_t>, int_t, dictcmp> syms_dict, vars_dict;
	std::vector<cws> syms;
	std::vector<size_t> lens;
	std::vector<std::map<int_t, std::wstring>> strs;
	std::pair<cws, size_t> dict_get(int_t t) const;
	std::set<wstr> strs_extra;
	std::vector<std::set<size_t>> builtin_symbdds;
	std::set<size_t> builtin_rels;
	int_t dict_get(cws s, size_t len);
	int_t dict_get(const lexeme& l);
	int_t dict_get(const std::wstring& s);
	size_t nsyms() const { return syms.size() + nums; }
	size_t dict_bits() const { return msb(nsyms()); }
	term get_term(const raw_term&);
	matrix get_rule(const raw_rule&);
	void term_pad(term& t, size_t ar);
	void rule_pad(matrix& t, size_t ar);
	matrix rule_pad(const matrix& t, size_t ar);
	std::vector<lp*> progs;
	std::vector<std::set<matrix>> proofs;
	bool mult = false;
	int_t nums = 0;
	template<typename V> std::set<matrix>
	from_func(V f, std::wstring name, size_t from, size_t to);
public:
	driver(FILE *f, bool proof);
	void progs_read(wstr s, bool proof);
	void prog_add(std::set<matrix> m, size_t ar,
		const std::map<int_t,std::wstring>& s, std::set<matrix>* proof);
	bool pfp(lp *p, std::set<matrix>* proof, size_t *padd);
	bool pfp(bool proof);
	std::wostream& printbdd(std::wostream& os, const matrix& t) const;
	std::wostream& printbdd(std::wostream& os, size_t t) const;
	std::wostream& printbdd(std::wostream& os, size_t t, size_t bits,
		size_t ar) const;
	std::wostream& printbdd_one(std::wostream& os, size_t t) const;
	std::wostream& printbdd_one(std::wostream& os, size_t t, size_t bits,
		size_t ar) const;
	std::wostream& printdb(std::wostream& os, size_t prog) const;
	~driver() {for (lp* p:progs) delete p; for (wstr w:strs_extra) free(w);}
};

#ifdef DEBUG
extern driver* drv;
std::wostream& printbdd(std::wostream& os,size_t t);
std::wostream& printbdd(std::wostream& os, size_t t, size_t bits, size_t ar);
std::wostream& printbdd_one(std::wostream& os,size_t t);
std::wostream& printbdd_one(std::wostream& os,size_t t, size_t bits, size_t ar);
#endif
