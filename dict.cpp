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
#include "driver.h"
using namespace std;

pair<cws, size_t> driver::dict_get(int_t t) const {
	static wchar_t str_nums[20], str_chr[] = L"'a'";
	if (t < chars) { str_chr[1] = t; return { str_chr, (size_t)3 }; }
	if ((t -= chars) < nums)
		return wcscpy(str_nums, to_wstring(t).c_str()),
			pair<cws, size_t>{ str_nums, wcslen(str_nums) };
	return { syms[t - nums], lens[t - nums] };
}

int_t driver::dict_get(cws s, size_t len, bool rel) {
	if (iswdigit(*s)) parse_error(err_digit, s, len);
	auto it = syms_dict.end();
	if (*s == L'?') {
		if (rel) parse_error(err_var_relsym, s, len);
		if ((it = vars_dict.find({s, len}))!= vars_dict.end())
			return it->second;
		int_t r = -vars_dict.size() - 1;
		return vars_dict[{s, len}] = r;
	}
	if (rel) return	(it=rels_dict.find({s, len})) != rels_dict.end()
			? it->second : (syms.push_back(s), lens.push_back(len),
			rels_dict[{s,len}] = syms.size() + nums + chars - 1);
	if ((it=syms_dict.find({s, len})) != syms_dict.end()) return it->second;
	return	syms.push_back(s), lens.push_back(len), syms_dict[{s,len}] =
		syms.size() + nums + chars - 1;
}

int_t driver::dict_get(const lexeme& l) {
	return dict_get(l[0], l[1]-l[0], false);
}

int_t driver::dict_get_rel(const lexeme& l) {
	return dict_get(l[0], l[1]-l[0], true);
}

int_t driver::dict_get_rel(const wstring& s) {
	auto it = rels_dict.find({s.c_str(), s.size()});
	if (it != rels_dict.end()) return it->second;
	wstr w = wcsdup(s.c_str());
	strs_extra.emplace(w);
	return	syms.push_back(w), lens.push_back(s.size()),
		rels_dict[{w, s.size()}] = syms.size() + nums + chars - 1;
}
/*
int_t driver::dict_get() {
	static size_t last = 1;
	return dict_get(wstring(L"%") + to_wstring(last));
}*/
