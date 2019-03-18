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
	assert(t);
	static wchar_t str_nums[20], str_chr[] = L"'a'";
	if (t > nums) return { syms[t - nums], lens[t - nums] };
	if (t < 256) { str_chr[1] = --t; return { str_chr, (size_t)3 }; }
	wcscpy(str_nums, to_wstring(t-256).c_str());
	return { str_nums, wcslen(str_nums) };
}

int_t driver::dict_get(cws s, size_t len) {
	if (!s) return pad;
	if (iswdigit(*s)) er("symbol name cannot begin with a digit");
	if (*s == L'?') {
		auto it = vars_dict.find({s, len});
		if (it != vars_dict.end()) return it->second;
		int_t r = -vars_dict.size() - 1;
		return vars_dict[{s, len}] = r;
	}
	auto it = syms_dict.find({s, len});
	if (it != syms_dict.end()) return it->second;
	return	syms.push_back(s), lens.push_back(len), syms_dict[{s,len}] =
		syms.size() + nums - 1;
}

int_t driver::dict_get(const lexeme& l) { return dict_get(l[0], l[1]-l[0]); }

int_t driver::dict_get(const wstring& s) {
	auto it = syms_dict.find({s.c_str(), s.size()});
	if (it != syms_dict.end()) return it->second;
	wstr w = wcsdup(s.c_str());
	strs_extra.emplace(w);
	return	syms.push_back(w), lens.push_back(s.size()),
		syms_dict[{w, s.size()}] = syms.size() + nums - 1;
}

int_t driver::dict_get() {
	static size_t last = 1;
	return dict_get(wstring(L"%") + to_wstring(last));
}
