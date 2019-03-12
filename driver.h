#include "tml.h"

struct dictcmp {
	bool operator()(const std::pair<wstr, size_t>& x,
			const std::pair<wstr, size_t>& y) const {
		return	x.second != y.second ? x.second < y.second :
			wcsncmp(x.first, y.first, x.second) < 0;
	}
};

class driver {
	std::map<std::pair<wstr, size_t>, int_t, dictcmp> syms_dict, vars_dict;
	std::vector<wstr> syms;
	std::vector<size_t> lens;
	std::vector<std::map<int_t, std::wstring>> strs;
	std::pair<wstr, size_t> dict_get(int_t t) const;
	int_t dict_get(wstr s, size_t len);
	size_t nums = 0;
	size_t nsyms() const { return syms.size() + nums; }
	size_t dict_bits() const { return msb(nsyms()-1); }
	int_t str_read(wstr *s); // parse a string and returns its dict id
	term term_read(wstr *s); // read raw term (no bdd)
	matrix rule_read(wstr *s); // read raw rule (no bdd)
	std::vector<lp*> progs;
	std::vector<std::set<matrix>> proofs;
	bool mult = false;
public:
	driver();
	std::set<matrix> prog_read(wstr *s, std::map<int_t, std::wstring>&strs);
	void progs_read(wstr s, bool proof);
	lp* prog_create(std::set<matrix> m, bool proof);
	bool pfp(lp *p, std::set<matrix>* proof);
	bool pfp(bool proof);
	std::wostream& printbdd(std::wostream& os, size_t prog, size_t t) const;
	std::wostream& printbdd(std::wostream& os, const matrix& t,
		size_t prog) const;
	std::wostream& printbdd(std::wostream& os, size_t t) const;
	std::wostream& printdb(std::wostream& os, size_t prog) const;
	~driver() { for (lp* p : progs) delete p; }
};

#ifdef DEBUG
extern driver* drv;
std::wostream& printbdd(std::wostream& os,size_t t){return drv->printbdd(os,t);}
#endif
