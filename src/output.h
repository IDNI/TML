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
#include "types.h"

extern std::wostream wcnull;

class output {
	static std::map<std::wstring, output> outputs;
	static std::wstring named; // filename w/o ext (used for @name)
	std::wstring n = L"";      // name of the output stream
	std::wstring e = L"";      // filename extension
	std::wstring t = L"@null"; // target
	std::wstring f;            // filename
	std::wostream* s;          // output stream
	std::wstringstream bs{L""};// buffer stream output
	std::wofstream fs;         // file stream output
	std::wostream& os(std::wostream* wos) { s = wos; return *s; }
public:
	static output& create(std::wstring n,std::wstring e,std::wstring t=L""){
		auto it = outputs.find(n);
		if (it == outputs.end())
			it = outputs.emplace(n, output(n, e)).first;
		if (it != outputs.end() && t != L"") it->second.target(t);
		return it->second;
	}
	static const std::wstring& set_name(const std::wstring fn = L"") {
		return named = fn;
	}
	static bool exists(const std::wstring nam) {
		auto it = outputs.find(nam);
		return it != outputs.end();
	}
	static output* get(const std::wstring nam) {
		auto it = outputs.find(nam);
		if (it == outputs.end()) return 0;
		return &(it->second);
	}
	static std::wostream& to(const std::wstring nam) {
		output* o = get(nam);
		return o && L"@null" != o->target() ? *o->s : wcnull;
	}
	static std::wstring get_target(const std::wstring nam) {
		output* o = get(nam);
		return o ? o->target() : L"@null";
	}
	static std::wostream& set_target(const std::wstring nam,
						const std::wstring tar) {
		output *o = get(nam);
		return o ? o->target(tar) : wcnull;
	}
	static bool is_null(const std::wstring nam) {
		output *o = get(nam);
		return !o || o->is_null();
	}
	static std::wstring file(const std::wstring nam) {
		output *o = get(nam);
		return o ? o->filename() : L"";
	}
	static std::wstring read(std::wstring nam) {
		output *o = get(nam);
		return o && o->target() == L"@buffer" && o->bs.good()
			? o->bs.str() : L"";
	}
	output() = delete;
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
		if (t==L"@buffer") { bs.str(L""); return os(&bs); }
		if (t==L"@name") {
			if (named != L"") filename(named+e);
			else return o::err()<<L"output '"<<n<<"' targeting "
					"@name without setting name"<<std::endl,
				os(&wcnull);
		} else filename(t);
		fs.open(ws2s(filename()));
		return os(&fs);
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
