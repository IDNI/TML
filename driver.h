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
#include <map>
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
	std::pair<cws, size_t> dict_get(int_t t) const;
	int_t dict_get(cws s, size_t len);
	int_t dict_get(const lexeme& l);
	int_t dict_get(const std::wstring& s);
	int_t dict_get();
	size_t nsyms() const { return syms.size() + nums; }
//	size_t dict_bits() const { return msb(nsyms()); }
	typedef std::map<int_t, std::wstring> strs_t;
//	std::vector<std::map<int_t, std::wstring>> strs;
	std::set<wstr> strs_extra;
	std::set<size_t> builtin_rels, builtin_symbdds;

	matrices get_char_builtins();
	term get_term(const raw_term&);
	matrix get_rule(const raw_rule&);
	void term_pad(term& t, size_t ar);
	void rule_pad(matrix& t, size_t ar);
	matrix rule_pad(const matrix& t, size_t ar);

	lp* prog = 0;
	bool mult = false;
	int_t nums = 0;

	template<typename V, typename X>
	void from_func(V f, std::wstring name, X from, X to, matrices&);
	strs_t directives_load(const raw_prog& p);
//	void calc_lens(const raw_prog& rp, size_t& ar);
	void prog_init(const raw_prog& rp, const matrices& rtxt, const strs_t&);
	void progs_read(wstr s);
	bool pfp(lp *p);
	driver(const raw_progs& rp);
public:
	driver(FILE *f);
	driver(std::wstring);
	bool pfp();

	std::wostream& printbdd(std::wostream& os, const matrix& t) const;
	std::wostream& printbdd(std::wostream& os, const lp *p, size_t t) const;
	std::wostream& printbdd_one(std::wostream& os, const lp *p, size_t t)
		const;
	std::wostream& printdb(std::wostream& os, const lp*) const;
	~driver() { if (prog) delete prog; for (wstr w:strs_extra) free(w);}
};

#ifdef DEBUG
extern driver* drv;
std::wostream& printdb(std::wostream& os, const lp*);
std::wostream& printbdd(std::wostream& os, const lp*, size_t t);
std::wostream& printbdd_one(std::wostream& os, const lp*, size_t t);
#endif
