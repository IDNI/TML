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
#ifndef __OPTIONS_H__
#define __OPTIONS_H__
#include <functional>
#include <iostream>
#include "defs.h"
#include "output.h"

typedef std::vector<std::string> strings;
typedef std::vector<std::wstring> wstrings;

struct option {
	enum type { UNDEFINED, INT, BOOL, STRING };
	struct value {
		value()               : t(UNDEFINED)         {}
		value(int i)          : t(INT),      v_i(i)  {}
		value(bool b)         : t(BOOL),     v_b(b)  {}
		value(std::wstring s) : t(STRING),   v_s(s)  {}
		void set(int i)          { t=INT;    v_i = i; }
		void set(bool b)         { t=BOOL;   v_b = b; }
		void set(std::wstring s) { t=STRING; v_s = s; }
		void null() {
			switch (t) {
				case INT:    v_i = 0; break;
				case BOOL:   v_b = false; break;
				case STRING: v_s = L""; break;
				default: ;
			}
		}
		type get_type() const { return t; }
		int                 get_int()    const { return v_i; }
		bool                get_bool()   const { return v_b; }
		const std::wstring& get_string() const { return v_s; }
		bool is_undefined() const { return t == UNDEFINED; }
		bool is_int()       const { return t == INT; }
		bool is_bool()      const { return t == BOOL; }
		bool is_string()    const { return t == STRING; }
		bool operator ==(const value& ov) const {
			if (t != ov.get_type()) return false;
			switch (t) {
				case UNDEFINED: return ov.is_undefined();
				case INT:       return v_i == ov.get_int();
				case BOOL:      return v_b == ov.get_bool();
				case STRING:    return v_s == ov.get_string();
			}
		}
	private:
		type         t;
		int          v_i = 0;
		bool         v_b = false;
		std::wstring v_s = L"";
	};
	typedef std::function<void(const value&)> callback;
	option() {}
	option(type t, wstrings n, callback e, option::value v={})
		: t(t), n(n), v(v), e(e) {}
	option(type t, wstrings n, option::value v={})
		: t(t), n(n), v(v), e(0) {}
	const std::wstring& name() const { return n[0]; }
	const wstrings& names() const { return n; }
	type get_type() const { return t; }
	value get() const { return v; }
	bool          is_output () const { return output::exists(name()); }
	bool          is_input  () const { return n[0]==L"input"||n[0]==L"i"; }
	int           get_int   () const { return v.get_int(); };
	bool          get_bool  () const { return v.get_bool(); };
	std::wstring  get_string() const { return v.get_string(); };
	bool operator ==(const value& ov) const { return v == ov; }
	bool operator ==(const option& o) const { return n == o.names(); }
	bool operator  <(const option& o) const { return n < o.names(); }
	void parse_value(const std::wstring& s) {
		//DBG(o::out() << L"option::parse_value(s=\"" << s <<
		//	L"\") <" << (int)t << L'>' << std::endl;)
		switch (t) {
			case INT: if (s != L"") v.set(std::stoi(s)); break;
			case BOOL: parse_bool(s); break;
			case STRING:
				if (s == L"") {
					if (is_output())
						v.set(std::wstring(L"@stdout"));
				} else v.set(s); break;
			default: throw 0;
		}
		if (e) e(v);
	}
	void parse_bool(const std::wstring& s) {
		if (s==L"" || s==L"true" || s==L"t" || s==L"1" || s==L"on" ||
						s==L"enabled" || s==L"yes")
			return v.set(true), (void)0;
		v.set(false);
		if (!(s==L"false" || s==L"f" || s==L"0" || s==L"off" ||
						s==L"disabled" || s==L"no"))
			o::err() << L"Wrong bool argument: " << s << std::endl;
	}
	void disable() {
		if (STRING == get_type() && is_output()) parse_value(L"@null");
		else v.null();
	}
	bool is_undefined() const { return v.is_undefined(); }
	option &description(const std::wstring& d) { return desc = d, *this; }
	std::wostream& help(std::wostream& os) const {
		std::wstringstream ss; ss << L"";
		long pos = ss.tellp();
		ss << L"\t";
		for (size_t i = 0; i != n.size(); ++i) {
			if (i) ss << L",";
			ss << L"--" << n[i];
		}
		ss << L" [";
		switch (t) {
			case INT: ss << "number"; break;
			case BOOL: ss << "bool"; break;
			case STRING:
				if (is_output()) ss << "output";
				else if (is_input()) ss << "input";
				else ss << "string";
				break;
			default: throw 0;
		}
		ss << L']';
		if (desc.size() > 0) {
			const long indent = 28;
			long to_write = indent-(((long)ss.tellp())-pos);
			if (to_write > 0) while (to_write-- > 0) ss << L' ';
			ss << L' ' << desc;
		}
		return os << ss.str();
	}
private:
	type t;
	wstrings n; // vector of name and alternative names (shortcuts)
	value v;
	callback e; // callback with value as argument, fired when option parsed
	std::wstring desc = L"";
};

class options {
	friend std::wostream& operator<<(std::wostream&, const options&);
	std::map<std::wstring, option> opts = {};
	std::map<std::wstring, std::wstring> alts = {};
	std::vector<std::wstring> args;
	std::wstring input_data = L"";
	bool parse_option(const wstrings &wargs, const size_t &i);
	bool is_value(const wstrings &wargs, const size_t &i);
	void setup();
	void init_defaults();
public:
	options()                      { setup(); }
	options(int argc, char** argv) { setup(); parse(argc, argv); }
	options(strings args)          { setup(); parse(args); }
	options(wstrings args)         { setup(); parse(args); }
	int argc()               const { return args.size(); }
	std::wstring argv(int n) const { if (n<argc()) return args[n]; throw 0;}
	void add(option o);
	bool get(std::wstring name, option& o) const;
	void set(const std::wstring name, const option o) {
		opts.insert_or_assign(name, o);
	}
	void parse(int argc, char** argv, bool internal = false);
	void parse(strings sargs,         bool internal = false);
	void parse(wstrings wargs,        bool internal = false);
	bool enabled (const std::wstring &arg) const;
	bool disabled(const std::wstring &arg) const { return !enabled(arg); }
	int           get_int   (std::wstring name) const;
	bool          get_bool  (std::wstring name) const;
	std::wstring  get_string(std::wstring name) const;
	void help(std::wostream& os) const;
	const std::wstring& input() const { return input_data; }
	void add_input_data(const std::wstring& data) { input_data += data; }
};

std::wostream& operator<<(std::wostream&, const std::map<std::wstring,option>&);
std::wostream& operator<<(std::wostream&, const option&);
std::wostream& operator<<(std::wostream&, const options&);
#endif
