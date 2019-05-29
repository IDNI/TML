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

std::wstring s2ws(const std::string&);
std::string  ws2s(const std::wstring&);

extern std::wostream wcnull;

class output {
	static std::map<std::wstring, output*> outputs;
	static std::wstring named; // filename w/o ext (used for @name)
	std::wstring n = L"";      // name of the output stream
	std::wstring e = L"";      // filename extension
	std::wstring t = L"@null"; // target
	std::wstring f;            // filename
	std::wostream* s;          // output stream
	std::wostream& os(std::wostream* wos) {
		return s = wos, *s;
	}
	std::wstring tmpfile() {
		std::wstring fn = s2ws(tmpnam(0)) + e;
		std::wcerr << fn << L" # " << n <<std::endl;
		return fn;
	}
	static output* add(output* o) { return outputs[o->name()] = o; }
	output(std::wstring n, std::wstring e) : n(n), e(e) {
		add(this);
	}
public:
	static output* create(std::wstring n, std::wstring e,
		std::wstring t = L"") {
		output* o = new output(n, e);
		if (t != L"") o->target(t);
		return o;
	}
	static const std::wstring& set_name(const std::wstring fn = L"") {
		return named = fn;
	}
	static output* get(const std::wstring nam) {
		auto it = outputs.find(nam);
		if (it == outputs.end()) return 0;
		return it->second;
	}
	static std::wostream& to(const std::wstring nam) {
		output *o = get(nam);
		if (!o || !o->s) return wcnull;
		return *o->s;
	}
	static std::wstring get_target(const std::wstring nam) {
		output *o = get(nam);
		return o ? o->target() : L"@null";
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
		return o && o->target() == L"@buffer"
			? ((std::wstringstream*)o->s)->str() : L"";
	}
	output() {}
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
		if ((t==L"@name" && named==L"") ||
			 t==L"@tmp")  filename(tmpfile());
		else if (t==L"@name") filename(named+e);
		else                  filename(t);
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
