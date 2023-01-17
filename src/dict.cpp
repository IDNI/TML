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

namespace idni {

dict_t::dict_t() {}
dict_t::~dict_t() { for (auto x : strs_allocated) free((char *)x); }

int_t dict_t::get_var(const lexeme& l) {
	auto it = vars_dict.find(l);
	if (it != vars_dict.end()) return it->second;
	int_t r = -vars_dict.size() - 1;
	vars.push_back(l);
	return vars_dict[l] = r;
}

int_t dict_t::get_rel(const lexeme& l) {
	auto it = rels_dict.find(l);
	if (it != rels_dict.end()) return it->second;
	rels.push_back(l);
	return rels_dict[l] = rels.size() - 1;
}

int_t dict_t::get_sym(const lexeme& l) {
	auto it = syms_dict.find(l);
	if (it != syms_dict.end()) return it->second;
	syms.push_back(l);
	return syms_dict[l] = syms.size()-1;
}

int_t dict_t::get_bltin(const lexeme& l) {
	if (*l[0] == '?') parse_error(err_var_relsym, l);
	auto it = bltins_dict.find(l);
	if (it != bltins_dict.end()) return it->second;
	bltins.push_back(l);
	return bltins_dict[l] = bltins.size() - 1;
}

int_t dict_t::get_new_sym() {
	static int_t cnt = 0;
	return get_sym(get_lexeme( "0s" + to_string(++cnt) ));
}

int_t dict_t::get_new_var() {
	static int_t cnt = 0;
	return get_var(get_lexeme("?0v" + to_string(++cnt)));
}

int_t dict_t::get_new_rel() {
	static int_t cnt = 0;
	string n = "0r" + to_string(++cnt);
	int_t nidx = get_rel(get_lexeme(n));
	return nidx;
	// TODO should we add a check for pre existing rel? The code could de 
	// as follows:
	//	size_t sz;
	//	lexeme l;
	//	retry: sz = rels.size(), l = get_lexeme(s + to_string_(last));
	//	rels.insert(l);
	//	if (rels.size() == sz) { ++last; goto retry; }
	//	return get_rel(l);
}

ints dict_t::get_rels(function<bool(const lexeme&)> filter) {
	ints filtered;
	for (size_t i = 0; i != rels.size(); ++i)
		if (!filter || filter(rels[i])) filtered.push_back(i);
	return filtered;
}

lexeme dict_t::get_lexeme(ccs w, size_t l) {
	if (l == (size_t)-1) l = strlen(w);
	auto it = strs_extra.find({ w, w + l });
	if (it != strs_extra.end()) return *it;
	char_t* r = strdup(w);
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

//---

int_t dict_t::get_temp_sym(const lexeme& l) {
	auto it = temp_syms_dict.find(l);
	if (it != temp_syms_dict.end()) return it->second;
	return temp_syms.push_back(l), temp_syms_dict[l] = (temp_syms.size());
}

int_t dict_t::get_fresh_temp_sym() {
	static int_t counter = 0;
	std::string fresh = "0tf" + to_string(++counter);
	int_t fresh_int = get_temp_sym(get_lexeme(fresh));
	return fresh_int;
}

lexeme dict_t::get_temp_sym(int_t t) const {
	return temp_syms[t-1];
}

} // idni namespace
