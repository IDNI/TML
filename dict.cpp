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
#include "dict.h"
using namespace std;

#define err_digit L"symbol name cannot begin with a digit.\n"
#define err_var_relsym L"relation symbol cannot be a variable.\n"

lexeme dict_t::get_sym(int_t t) const {
	static wchar_t str_nums[20], str_chr[] = L"'a'";
	if (t < chars) { str_chr[1] = t; return { str_chr, str_chr + 3 }; }
	if ((t -= chars) < nums)
		return wcscpy(str_nums, to_wstring(t).c_str()),
			lexeme{ str_nums, str_nums + wcslen(str_nums) };
	return syms[t - nums];
}

int_t dict_t::get_var(const lexeme& l) {
	assert(*l[0] == L'?');
	auto it = vars_dict.find(l);
	if (it != vars_dict.end()) return it->second;
	int_t r = -vars_dict.size() - 1;
	return vars_dict[l] = r;
}

int_t dict_t::get_rel(const lexeme& l) {
	if (*l[0] == L'?') parse_error(err_var_relsym, l);
	auto it = rels_dict.find(l);
	if (it != rels_dict.end()) return it->second;
	rels.push_back(l);
	return rels_dict[l] = rels.size() - 1;
}

int_t dict_t::get_sym(const lexeme& l) {
	auto it = syms_dict.find(l);
	if (it != syms_dict.end()) return it->second;
	syms.push_back(l);
	return syms_dict[l] = syms.size() + nums + chars - 1;
}

/*int_t dict_t::get(const lexeme& l, bool rel) {
	if (iswdigit(*s)) parse_error(err_digit, s, len);
	if (*s == L'?') return get_var(s, len);
	if (rel) return get_rel(s, len);
	return get_sym(s, len);
}*/

int_t dict_t::get_rel(const wstring& s) {
	return get_rel(get_lexeme(s));
/*	auto it = rels_dict.find({s.c_str(), s.size()});
	if (it != rels_dict.end()) return it->second;
	wstr w = wcsdup(s.c_str());
	lexeme l(w, w + s.size());
	strs_extra.insert(l);
	return rels.push_back(l), rels_dict[l] = rels.size() - 1;*/
}

lexeme dict_t::get_lexeme(const wstring& s) {
	cws w = s.c_str();
	auto it = strs_extra.find({w, w + s.size()});
	if (it != strs_extra.end()) return *it;
	wstr r = wcsdup(s.c_str());
	lexeme l = {r, r + s.size()};
	strs_extra.insert(l);
	return l;
}

void dict_t::add_chars(size_t newchars) {
	chars += newchars;
	for (auto& x : syms_dict) x.second += newchars;
}

void dict_t::add_nums(size_t newnums) {
	nums += newnums;
	for (auto& x : syms_dict) x.second += newnums;
}
