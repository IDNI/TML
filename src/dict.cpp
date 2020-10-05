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
#include <cstring>
#include "defs.h"
#include "dict.h"
#include "err.h"
#include "input.h"
using namespace std;

dict_t::dict_t() : op(get_lexeme("(")), cl(get_lexeme(")")) {}

dict_t::~dict_t() { for (auto x : strs_allocated) free((char *)x); }

lexeme dict_t::get_sym(int_t t) const {
	DBG(assert(!(t&1) && !(t&2) && syms.size()>(size_t)(t>>2));)
	static char_t str_nums[20], str_chr[] = { '\'', 'a', '\'' };
	if (t & 1) { str_chr[1] = t>>=2; return { str_chr, str_chr + 3 }; }
	if (t & 2) return strcpy(str_nums, to_string_t(t>>=2).c_str()),
			lexeme{ str_nums, str_nums + strlen(str_nums) };
	return syms[t>>2];
}

int_t dict_t::get_fresh_var(int_t old) {
	static int_t counter = 0;
	std::string fresh = "?0f" + to_string_(++counter) + to_string_(old);
	int_t fresh_int = get_var(get_lexeme(fresh));
	return fresh_int;
}

int_t dict_t::get_fresh_sym(int_t old) {
	static int_t counter = 0;
	std::string fresh = "0f" + to_string_(++counter) + to_string_(old);
	int_t fresh_int = get_sym(get_lexeme(fresh));
	return fresh_int;
}
int_t dict_t::get_var(const lexeme& l) {
	//DBG(assert(*l[0] == '?');)
	auto it = vars_dict.find(l);
	if (it != vars_dict.end()) return it->second;
	int_t r = -vars_dict.size() - 1;
	vars.push_back(l);
	return vars_dict[l] = r;
}

lexeme dict_t::get_var_lexeme_from(int_t r) {
	DBG(assert(r<0);)
	int index = (-r -1);
	if (index < (int_t)vars.size()) {
#ifdef DEBUG
		int nr =
#endif
			get_var(vars[index]);
		DBG(assert(nr == r);)
		return vars[index];
	}
	lexeme l = get_lexeme(string("?v") + to_string_(-r));
#ifdef DEBUG
	int nr =
#endif
		get_var(l) ;
	DBG(assert(nr == r));
	return l;
}

int_t dict_t::get_rel(const lexeme& l) {
	//if (*l[0] == L'?') parse_error(err_var_relsym, l);
	auto it = rels_dict.find(l);
	if (it != rels_dict.end()) return it->second;
	rels.push_back(l);
	return rels_dict[l] = rels.size() - 1;
}

int_t dict_t::get_sym(const lexeme& l) {
	auto it = syms_dict.find(l);
	if (it != syms_dict.end()) return it->second;
	return syms.push_back(l), syms_dict[l] = (syms.size()-1)<<2;
}

int_t dict_t::get_bltin(const lexeme& l) {
	if (*l[0] == '?') parse_error(err_var_relsym, l);
	auto it = bltins_dict.find(l);
	if (it != bltins_dict.end()) return it->second;
	bltins.push_back(l);
	return bltins_dict[l] = bltins.size() - 1;
}

lexeme dict_t::get_lexeme(ccs w, size_t l) {
	if (l == (size_t)-1) l = strlen(w);
	auto it = strs_extra.find({ w, w + l });
	if (it != strs_extra.end()) return *it;
	cstr r = strdup(w);
	strs_allocated.push_back(r);
	lexeme lx = { r, r + l };
	strs_extra.insert(lx);
	return lx;
}
lexeme dict_t::get_lexeme(const std::basic_string<unsigned char>& s) {
	ccs w = s.c_str();
	return get_lexeme(w, s.size());
}
lexeme dict_t::get_lexeme(const std::basic_string<char>& s) {
	ccs w = (ccs) s.c_str();
	return get_lexeme(w, s.size());
}

int_t dict_t::get_temp_sym(const lexeme& l) {
	auto it = temp_syms_dict.find(l);
	if (it != temp_syms_dict.end()) return it->second;
	return temp_syms.push_back(l), temp_syms_dict[l] = (temp_syms.size());
}

