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

dict_t::dict_t() {}
dict_t::~dict_t() { for (auto x : strs_allocated) free((char *)x); }

bool dict_t::is_valid_sym_val(int_t t) const {
	return bitunv ? (t >=2 && t <= (int_t) syms.size()+1) :
					(t>>2 >= 0 && t>>2 < (int_t) syms.size());
}

lexeme dict_t::get_sym(int_t t) const {
	if (bitunv == false) {
		DBG(assert(!(t&1) && !(t&2) && syms.size()>(size_t)(t>>2));)
		static char_t str_nums[20], str_chr[] = { '\'', 'a', '\'' };
		if (t & 1) { str_chr[1] = t>>=2; return { str_chr, str_chr + 3 }; }
		if (t & 2) return strcpy(str_nums, to_string_t(t>>=2).c_str()),
				lexeme{ str_nums, str_nums + strlen(str_nums) };
		return syms[t>>2];
	}
	else {
		DBG(assert(t>=0));
		static char_t str_num[] = { '\'', 'a', '\'' };
		if (t == 1 || t == 0) { str_num[1] = t; return { str_num, str_num + 3 }; }
		DBG(assert(syms.size());)
		if( t >=2 && t <= (int_t) syms.size()+1)
			return syms[t-2]; // all known and valid symbols remain b/w >=2 and syms.size()-2;
		else return lexeme{(ccs)"BOT",(ccs)"BOT"+3 };
		//get_temp_sym(const_cast<dict_t*>(this)->get_fresh_temp_sym(t));
	}
}

int_t dict_t::get_fresh_var() {
	static int_t counter = 0;
	std::string fresh = "?0f" + to_string_(++counter);
	int_t fresh_int = get_var(get_lexeme(fresh));
	return fresh_int;
}

int_t dict_t::get_fresh_sym() {
	static int_t counter = 0;
	std::string fresh = "0f" + to_string_(++counter);
	int_t fresh_int = get_sym(get_lexeme(fresh));
	return fresh_int;
}
/*
lexeme driver::get_new_rel() {
	static int_t last = 0;
	string s = "r";
	size_t sz;
	lexeme l;
retry:	sz = rels.size(), l = get_lexeme(s + to_string_(last));
	rels.insert(l);
	if (rels.size() == sz) { ++last; goto retry; }
	return l;
}
*/
int_t dict_t::get_var(const lexeme& l) {
	//DBG(assert(*l[0] == '?');)
	auto it = vars_dict.find(l);
	if (it != vars_dict.end()) return it->second;
	int_t r = -vars_dict.size() - 1;
	vars.push_back(l);
	return vars_dict[l] = r;
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
	return syms.push_back(l),
	syms_dict[l] = !bitunv?(syms.size()-1)<<2:(syms.size()-1+2);
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


int_t dict_t::get_fresh_temp_sym() {
	static int_t counter = 0;
	std::string fresh = "0tf" + to_string_(++counter);
	int_t fresh_int = get_temp_sym(get_lexeme(fresh));
	return fresh_int;
}

lexeme dict_t::get_temp_sym(int_t t) const {
	return temp_syms[t-1];
}

ints dict_t::get_rels(function<bool(const lexeme&)> filter) {
	ints filtered;
	for (size_t i = 0; i != rels.size(); ++i)
		if (!filter || filter(rels[i])) filtered.push_back(i);
	return filtered;
}
