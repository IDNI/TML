#ifndef __STRINGS_H__
#define __STRINGS_H__
#include <map>
#include <string>
#include <vector>
#include <iostream>
#include <cstdint>

using std::vector;
using std::map;
using std::wstring;
using std::wostream;

#ifdef _DEBUG
#define DEBUG(x) (wcout<<x).flush()
#else
#define DEBUG(x)
#endif

const wchar_t err_misquote[]  = L"The only quotable chars are ()->=\\\"";
const wchar_t err_relvars[]   = L"Relation variables are not allowed";
const wchar_t err_eq_in_head[]= L"Equality not allowed in head";
const wchar_t err_expected1[] = L"Expected ( or =";
const wchar_t err_expected2[] = L"Unexpected character";
const wchar_t err_expected3[] = L"Expected . or ->";
const wchar_t err_expected4[] = L"Expected '.'";

uint64_t lphash(const int32_t& t);
class dict_t {
	vector<wstring> strings;
	map<wstring, size_t> m;
public:
	int32_t operator[](const wstring&);
	wstring operator[](int32_t) const;
	friend wostream& operator<<(wostream &os, const dict_t&);
};
extern dict_t dict;

struct strbuf {
	const wchar_t *s;
	strbuf(const wchar_t *s) : s(s) {}
	strbuf& operator++() { ++s; return *this; }
	wchar_t operator*() const { return *s; }
	intptr_t operator-(const strbuf& t) const { return s - t.s; }
	wchar_t adv() { return *s++; }
};
#endif
