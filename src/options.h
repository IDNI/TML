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
#include "input.h"
#include "output.h"

class archive;

struct option {
	friend class archive;
	enum type { UNDEFINED, INT, BOOL, STRING };
	struct value {
		friend class archive;
		value()              : t(UNDEFINED)         {}
		value(int i)         : t(INT),      v_i(i)  {}
		value(bool b)        : t(BOOL),     v_b(b)  {}
		value(std::string s) : t(STRING),   v_s(s)  {}
		void set(int i)         { t=INT;    v_i = i; }
		void set(bool b)        { t=BOOL;   v_b = b; }
		void set(std::string s) { t=STRING; v_s = s; }
		void null() {
			switch (t) {
				case INT:    v_i = 0;     break;
				case BOOL:   v_b = false; break;
				case STRING: v_s = "";    break;
				default: ;
			}
		}
		type get_type() const { return t; }
		int                get_int()    const { return v_i; }
		bool               get_bool()   const { return v_b; }
		const std::string& get_string() const { return v_s; }
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
		type        t;
		int         v_i = 0;
		bool        v_b = false;
		std::string v_s = "";
	} v;
	typedef std::function<void(const value&)> callback;
	option() {}
	option(type t, strings n, callback e, option::value v={})
		: v(v), t(t), n(n), e(e) {}
	option(type t, strings n, option::value v={})
		: v(v), t(t), n(n), e(0) {}
	const std::string& name() const { return n[0]; }
	const strings& names() const { return n; }
	type get_type() const { return t; }
	value get() const { return v; }
	bool          is_output () const { return outputs::exists(name()); }
	bool          is_input  () const { return n[0]=="input" || n[0]=="i"; }
	int           get_int   () const { return v.get_int(); };
	bool          get_bool  () const { return v.get_bool(); };
	std::string  get_string() const { return v.get_string(); };
	bool operator ==(const value& ov) const { return v == ov; }
	bool operator ==(const option& o) const { return n == o.names(); }
	bool operator  <(const option& o) const { return n < o.names(); }
	void parse_value(const std::string& s) {
		//DBG(o::out() << "option::parse_value(s=\"" << s <<
		//	"\") <" << (int)t << '>' << std::endl;)
		switch (t) {
			case INT: if (s != "") v.set(std::stoi(s)); break;
			case BOOL: parse_bool(s); break;
			case STRING: if (s != "") v.set(s);
				else if (is_output()) v.set("@stdout");
				break;
			default: DBGFAIL;
		}
		if (e) e(v);
	}
	void parse_bool(const std::string& s) {
		if (s=="" || s=="true" || s=="t" || s=="1" || s=="on" ||
						s=="enabled" || s=="yes")
			return v.set(true), (void)0;
		v.set(false);
		if (!(s=="false" || s=="f" || s=="0" || s=="off" ||
						s=="disabled" || s=="no"))
			o::err() << "Wrong bool argument: " << s << std::endl;
	}
	void disable() {
		if (STRING == get_type() && is_output()) parse_value("@null");
		else v.null();
	}
	bool is_undefined() const { return v.is_undefined(); }
	option &description(const std::string& d) { return desc = d, *this; }
	template <typename T>
	std::basic_ostream<T>& help(std::basic_ostream<T>& os) const {
		std::basic_ostringstream<T> ss; ss << "";
		long pos = ss.tellp();
		ss << "\t";
		for (size_t i = 0; i != n.size(); ++i)
			ss << (i ? ", " : "-") << "-" << n[i];
		ss << " [";
		switch (t) {
			case INT: ss << "number"; break;
			case BOOL: ss << "bool"; break;
			case STRING:
				if (is_output()) ss << "output";
				else if (is_input()) ss << "input";
				else ss << "string";
				break;
			default: DBGFAIL;
		}
		ss << "]";
		if (desc.size() > 0) {
			const long indent = 28;
			long to_write = indent-(((long)ss.tellp())-pos);
			if (to_write > 0) while (to_write-- > 0) ss << " ";
			ss << ' ' << desc;
		}
		return os << ss.str();
	}
private:
	type t;
	strings n;  // vector of name and alternative names (shortcuts)
	callback e; // callback with value as argument, fired when option parsed
	std::string desc = "";
};

class options {
	friend class archive;
public:
	options() : options(0, 0) {}
	options(inputs *ii, outputs *oo) : ii(ii), oo(oo) { setup(); }
	options(int argc, char** argv, inputs *ii = 0, outputs *oo = 0) :
		ii(ii), oo(oo) { setup(); parse(argc, argv); }
	options(strings args, inputs *ii = 0, outputs *oo = 0):
		ii(ii), oo(oo){ setup(); parse(args); }
	options(wstrings args, inputs *ii = 0, outputs *oo = 0):
		ii(ii), oo(oo){ setup(); parse(args); }
	int argc() const { return args.size(); }
	std::string argv(int n) const {
		if (n<argc()) return args[n];
		DBGFAIL; return "";
	}
	void add(option o);
	bool get(std::string name, option& o) const;
	void set(const std::string name, const option o) {
		opts.insert_or_assign(name, o);
	}
	template <typename T>
	void set(const std::string &name, T val);
	void set_outputs(outputs* oo);
	void parse(int argc, char** argv, bool internal = false);
	void parse(strings  sargs,    bool internal = false);
	void parse(wstrings wargs,    bool internal = false);
	void enable(const std::string &arg);
	void disable(const std::string &arg);
	bool enabled (const std::string &arg) const;
	bool disabled(const std::string &arg) const { return !enabled(arg); }
	int         get_int   (std::string name) const;
	bool        get_bool  (std::string name) const;
	std::string get_string(std::string name) const;
	template <typename T> void help(std::basic_ostream<T>&) const;
	inputs* get_inputs() const { return ii; }
private:
	template <typename T> friend std::basic_ostream<T>& operator<<(std::basic_ostream<T>&, const options&);
	inputs*  ii;
	outputs* oo;
	std::map<std::string, option> opts = {};
	std::map<std::string, std::string> alts = {};
	std::vector<std::string> args;
	std::string input_data = "";
	bool parse_option(const strings &sargs, const size_t &i);
	bool is_value(const strings &sargs, const size_t &i);
	void setup();
	void init_defaults();
};

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>&, const std::map<std::string, option>&);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>&, const option&);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>&, const options&);
#endif
