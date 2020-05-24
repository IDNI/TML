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
#include "err.h"
#include "input.h"
using namespace std;

#define mkchr(x) (int_t(x))
#define mknum(x) (int_t(x))
#define mksym(x) (int_t(x))
#define un_mknum(x) (int_t(x))

//int_t get_int_t(cws from, cws to); // input.cpp, TODO: put in header

dict_t::dict_t() : op(get_lexeme(L"(")), cl(get_lexeme(L")")) {}

dict_t::~dict_t() { for (auto x : strs_extra) free((wstr)x[0]); }

// TODO: D: just temp...
lexeme get_lexeme(const wstring& s) {
	cws w = s.c_str();
	wstr r = wcsdup(w);
	lexeme l = { r, r + s.size() };
	return l;
}

lexeme dict_t::get_sym(int_t t) const {
	if (!(t < syms.size())) throw out_of_range("get_sym: index.");
	return syms[un_mknum(t)];
}

int_t dict_t::get_fresh_var(int_t old) {

	static int_t counter=0;
	wstring fresh = L"?0f"+ to_wstring(++counter)+to_wstring(old);
	int_t fresh_int = get_var(get_lexeme(fresh));
	return fresh_int;
}

int_t dict_t::get_fresh_sym(int_t old) {

	static int_t counter=0;
	wstring fresh = L"0f" + to_wstring(++counter)+to_wstring(old);
	int_t fresh_int = get_sym(get_lexeme(fresh));
	return fresh_int;
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
	return syms.push_back(l), syms_dict[l] = mksym(syms.size()-1);
}

int_t dict_t::get_bltin(const lexeme& l) {
	if (*l[0] == L'?') parse_error(err_var_relsym, l);
	auto it = bltins_dict.find(l);
	if (it != bltins_dict.end()) return it->second;
	bltins.push_back(l);
	return bltins_dict[l] = bltins.size() - 1;
}

bool equals(cws l0, cws l1, cws s) {
	size_t n = wcslen(s);
	return (size_t)(l1 - l0) != n ? false : !wcsncmp(l0, s, n);
}

int_t get_index(const lexeme& l) {
	if (*l[0] != L'[') parse_error(err_eof, l);
	if ((size_t)(l[1] - l[0]) < 3) parse_error(err_eof, l); // [0]
	cws fst = l[0], snd = fst+1, esnd = nullptr;
	while (*++fst && fst != l[1]) {
		if (esnd != nullptr) { // chars after ], not allowed
			parse_error(err_eof, l);
			break;
		}
		if (*fst == L']') esnd = fst;
	}
	if (!esnd) parse_error(err_eof, l); // has [ but no ]
	return get_int_t(snd, esnd); // TODO: default bitness?
	//return size_t(get_int_t(snd, esnd)); // TODO: default bitness?
}

// use dict just to store type strings, avoid duplicate parsing.
int_t dict_t::get_type(const lexeme& l) {
	size_t nums = 0;
	return get_type(l, nums);
}

/* 
 - nums is any outside value for that term + we set it up if defined within type
*/
int_t dict_t::get_type(const lexeme& l, int_t nums) {
	//nums = 0;
	if (*l[0] != L':') parse_error(err_eof, l);
	auto it = types_dict.find(l);
	if (it != types_dict.end()) return it->second;

	cws fst = l[0], efst = nullptr, snd = nullptr, esnd = nullptr;
	while (*++fst && fst != l[1]) {
		if (esnd != nullptr) { // chars after ], not allowed
			nums = get_index(lexeme{ esnd+1, l[1]});
			//parse_error(err_eof, l);
			break;
		}
		if (*fst == L'[') efst = fst; // snd = fst + 1;
		else if (*fst == L']') esnd = fst;
	}
	if (efst && !esnd) parse_error(err_eof, l); // has [ but no ]
	fst = l[0] + 1;
	//efst = efst ? efst : l[1]; // if (!efst || !esnd) snd = esnd = 0;
	if (!efst) efst = l[1], snd = esnd = 0;
	else if (!esnd) snd = esnd = 0;
	else snd = efst + 1; // , esnd = esnd;

	base_type type = base_type::NONE;
	if (equals(fst, efst, L"int")) type = base_type::INT;
	else if (equals(fst, efst, L"chr")) type = base_type::CHR;
	else if (equals(fst, efst, L"str")) type = base_type::STR;
	int_t bits = snd ? get_int_t(snd, esnd) : 0; // TODO: default bitness?

	types.emplace_back(type, bits, nums); // , fst, efst, snd, esnd);
	return types_dict[l] = types.size() - 1;
}

lexeme dict_t::get_lexeme(const wstring& s) {
	cws w = s.c_str();
	auto it = strs_extra.find({w, w + s.size()});
	if (it != strs_extra.end()) return *it;
	wstr r = wcsdup(w);
	lexeme l = {r, r + s.size()};
	strs_extra.insert(l);
	return l;
}

lexeme dict_t::make_lexeme(const wstring& s) const { // { //
	cws w = s.c_str();
	auto it = strs_extra.find({ w, w + s.size() });
	if (it != strs_extra.end()) return *it;
	wstr r = wcsdup(w);
	lexeme l = { r, r + s.size() };
	//strs_extra.insert(l);
	return l;
}
