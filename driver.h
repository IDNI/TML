#include "tml.h"
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
	int_t dict_get(cws s, size_t len);
	int_t dict_get(const lexeme& l);
	size_t nsyms() const { return syms.size() + nums; }
	size_t dict_bits() const { return msb(nsyms()-1); }
	term get_term(const raw_term&);
	matrix get_rule(const raw_rule&);
	std::vector<lp*> progs;
	std::vector<std::set<matrix>> proofs;
	bool mult = false;
	int_t nums = 0;
	size_t ar = 0;
public:
	driver(FILE *f, bool proof);
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
