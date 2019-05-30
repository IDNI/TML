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
#ifndef __OUTPUT_H__
#define __OUTPUT_H__
#include <string>
#include <sstream>
#include <map>
#include <fstream>
#include "defs.h"

extern std::wostream wcnull;

class output {
	static std::map<std::wstring, output> outputs;
	static std::wstring named; // filename w/o ext (used for @name)
	std::wstring n = L"";      // name of the output stream
	std::wstring e = L"";      // filename extension
	std::wstring t = L"@null"; // target
	std::wstring f;            // filename
	std::wostream* s;          // output stream
	std::wostream& os(std::wostream* wos) { return s = wos, *s; }
public:
	static output create(std::wstring n, std::wstring e,
						std::wstring t = L"") {
		auto it = outputs.emplace(n, output(n, e));
		if (t != L"") it.first->second.target(t);
		return it.first->second;
	}
	static const std::wstring& set_name(const std::wstring fn = L"") {
		return named = fn;
	}
	static bool exists(const std::wstring nam) {
		auto it = outputs.find(nam);
		return it != outputs.end();
	}
	static bool get(const std::wstring nam, output& o) {
		auto it = outputs.find(nam);
		if (it == outputs.end()) return false;
		return o = it->second, true;
	}
	static void set(const std::wstring nam, output o) {
		outputs.insert_or_assign(nam, o);
	}
	static std::wostream& to(const std::wstring nam) {
		output o;
		return get(nam, o) && o.s ? *o.s : wcnull;
	}
	static std::wstring get_target(const std::wstring nam) {
		output o;
		return get(nam, o) ? o.target() : L"@null";
	}
	static std::wostream& set_target(const std::wstring nam,
						const std::wstring tar) {
		output o;
		if (!get(nam, o)) return wcnull;
		std::wostream& os = o.target(tar);
		return set(nam, o), os;
	}
	static bool is_null(const std::wstring nam) {
		output o;
		return !get(nam, o) || o.is_null();
	}
	static std::wstring file(const std::wstring nam) {
		output o;
		return get(nam, o) ? o.filename() : L"";
	}
	static std::wstring read(std::wstring nam) {
		output o;
		return get(nam, o) && o.target() == L"@buffer"
			? ((std::wstringstream*)o.s)->str() : L"";
	}
	output() {}
	output(std::wstring n, std::wstring e) : n(n), e(e) {}
	std::wstring name() const { return n; }
	std::wstring filename() const { return f; }
	std::wstring filename(const std::wstring fn) { return f = fn; }
	std::wostream& os() const { return *s; }
	std::wstring target() const { return t; }
	std::wostream& target(const std::wstring tar) {
		t = tar == L"" ? L"@stdout" : tar;
		if (t==L"@null")   return os(&wcnull);
		if (t==L"@stdout") return os(&std::wcout);
		if (t==L"@stderr") return os(&std::wcerr);
		if (t==L"@buffer") return os(new std::wstringstream());
		if (t==L"@name") {
			if (named != L"") filename(named+e);
			else return std::wcerr<<L"output '"<<n<<
				"' targeting @name without name"<<std::endl,
				os(&wcnull);
		} else filename(t);
		return os(new std::wofstream(ws2s(filename())));
	}
	bool is_null() const {
		return t == L"@null" || outputs.find(n) == outputs.end();
	}
	bool operator ==(const output& o) const {
		return n == o.n && filename() == o.filename();
	}
	bool operator <(const output& o) const { return n < o.n; }
};
#endif
