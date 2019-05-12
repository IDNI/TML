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
#include <algorithm>
#include <string>
#include <set>

typedef enum dialect_t { TRANSFORMED, XSB, SWIPL, SOUFFLE } dialect_t;
typedef enum format_t { F_TML, F_CSV } format_t;
typedef enum token_formats_t { T_TML, T_JSON, T_XML, T_HTML } token_formats_t;

#define if_opt(o)       if (option(arg, (o)))
#define if_opts(o1, o2) if (option(arg, (o1)) || option(arg, (o2)))

struct options {
	std::set<format_t> format = { F_TML };
	std::set<dialect_t> dialect = {};
	std::set<token_formats_t> token_formats = {};
	options() {}
	options(int argc, char** argv) { parse(argc, argv); }
	void parse(int c, char** v) {
		for (int i = 1; i < c; ++i) {
			std::string arg = std::string(v[i]);
			if_opts("t", "transformed") dialect.insert(TRANSFORMED);
			else if_opt("xsb")          dialect.insert(XSB);
			else if_opt("swipl")        dialect.insert(SWIPL);
			else if_opt("souffle")      dialect.insert(SOUFFLE);
			else if_opt("csv")          format.insert(F_CSV);
			else if_opt("tokens")      token_formats.insert(T_TML);
			else if_opt("tokens-json") token_formats.insert(T_JSON);
			else if_opt("tokens-xml")  token_formats.insert(T_XML);
			else if_opt("tokens-html") token_formats.insert(T_HTML);
		}
	}
	bool option(const std::string arg, const std::string o) const {
		return (arg == "--"+o || arg == "-"+o);
	}
	template<class T> bool enabled(const std::set<T> &s, const T &o) const {
		auto it = std::find (s.begin(), s.end(), o);
		return (it != s.end());
	}
	bool enabled_dialect(const dialect_t d)const{return enabled(dialect,d);}
	bool enabled_format(const format_t f) const { return enabled(format,f);}
	bool enabled_token_formats(token_formats_t t) const {
		return enabled(token_formats, t); }
};
