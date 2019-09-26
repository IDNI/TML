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
#include "defs.h"
#include <map>

class dict_t {
	typedef std::map<lexeme, int_t, lexcmp> dictmap;
	dictmap syms_dict, vars_dict, rels_dict;
	std::vector<lexeme> syms, rels;
	std::set<lexeme, lexcmp> strs_extra;
public:
	dict_t();
	dict_t(const dict_t& d) : syms_dict(d.syms_dict),
		vars_dict(d.vars_dict), rels_dict(d.rels_dict), syms(d.syms),
		rels(d.rels), strs_extra(d.strs_extra), op(d.op), cl(d.cl) {}
	lexeme op, cl;
	const lexeme& get_rel(int_t t) const { return rels[t]; }
	lexeme get_sym(int_t t) const;
	int_t get_var(const lexeme& l);
	int_t get_rel(const lexeme& l);
	int_t get_sym(const lexeme& l);

	lexeme get_lexeme(const std::wstring& s);
	int_t get_rel(const std::wstring& s) { return get_rel(get_lexeme(s)); }
	size_t nsyms() const { return syms.size(); }
	size_t nvars() const { return vars_dict.size(); }
	size_t nrels() const { return rels.size(); }
	dict_t& operator=(const dict_t& d) {
		return syms_dict = d.syms_dict, vars_dict = d.vars_dict,
			rels_dict = d.rels_dict, syms = d.syms,
			rels = d.rels, strs_extra = d.strs_extra, op = d.op,
			cl = d.cl, *this;
	}
	~dict_t();
};
