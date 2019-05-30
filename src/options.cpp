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
#include "options.h"

using namespace std;

void options::add(option o) {
	set(o.name(), o);
	for (auto n : o.names()) alts[n] = o.name();
}

bool options::get(const wstring name, option& o) const {
	auto ait = alts.find(name);        if (ait == alts.end()) return false;
	auto oit = opts.find(ait->second); if (oit == opts.end()) return false;
	return o = oit->second, true;
}

int options::get_int(wstring name) const {
	option o; return get(name, o) ? o.get_int() : 0;
}

bool options::get_bool(wstring name) const {
	option o; return get(name, o) ? o.get_bool() : false;
}

wstring options::get_string(wstring name) const {
	option o; return get(name, o) ? o.get_string() : L"";
}

void options::parse(int argc, char** argv) {
	wstrings wargs = {};
	for (int i = 1; i < argc; ++i)
		wargs.push_back(s2ws(string(argv[i])));
	parse(wargs);
}

void options::parse(strings args) {
	wstrings wargs = {};
	for (size_t i=0; i < wargs.size(); ++i) wargs.push_back(s2ws(args[i]));
	parse(wargs);
}

void options::parse(wstrings args) {
	wstring v;
	for (size_t i = 0; i < args.size(); ++i) {
		v = (i < args.size()-1) ? try_read_value(args[i+1]) : L"";
		parse_option(args[i], v);
		if (v != L"") i++;
	}
}

bool options::enabled(const wstring name) const {
	option o;
	if (!get(name, o)) return false;
	switch (o.get_type()) {
		case option::type::BOOL:   return o.get_bool();
		case option::type::INT:    return o.get_int() > 0;
		case option::type::STRING: {
			return output::exists(o.name())
				? !output::is_null(o.name())
				: o.get_string() != L"";
		}
		default: ;
	}
	return false;
}

wstring options::try_read_value(wstring v) {
	if (v == L"-") return L"@stdout";
	if (v.rfind(L"---", 0) == 0) return v.substr(2);
	return v[0] == L'-' ? L"" : v;
}

void options::parse_option(wstring arg, wstring v) {
	option o;
	bool disabled = false;
	size_t pos = 0;
	// skip hyphens
	while (pos < arg.length() && arg[pos] == L'-' && pos < 2) ++pos;
	wstring a = arg.substr(pos);
	// is option disabled?
	if (a.rfind(L"disable-",   0) == 0) disabled = true, a = a.substr(8);
	else if (a.rfind(L"dont-", 0) == 0) disabled = true, a = a.substr(5);
	else if (a.rfind(L"no-",   0) == 0) disabled = true, a = a.substr(3);
	if (!get(a, o)) return;
	if (disabled) o.disable();
	else o.parse_value(v);
	set(o.name(), o);
}

#define add_output(n) add(option(option::type::STRING, {n}, \
		[](const option::value& v) { \
			output::set_target(n,v.get_string());}))
#define add_output_alt(n, alt) add(option(option::type::STRING, {n, alt}, \
		[](const option::value& v) { \
			output::set_target(n,v.get_string());}))

void options::setup() {

	add(option(option::type::BOOL,   { L"ms" }));
	add(option(option::type::BOOL,   { L"run" }));
	add(option(option::type::BOOL,   { L"csv" }));
	add(option(option::type::STRING, { L"name", L"n" },
		[](const option::value& v) {
			output::set_name(v.get_string());
		}));
	add_output_alt(L"output",      L"o");
	add_output_alt(L"transformed", L"t");
	add_output_alt(L"ast",         L"at");
	add_output_alt(L"ast-json",    L"aj");
	add_output_alt(L"ast-xml",     L"ax");
	add_output_alt(L"ast-html",    L"ah");
	add_output    (L"xsb");
	add_output    (L"swipl");
	add_output    (L"souffle");

	init_defaults();
}

#undef add_output
#undef add_output_alt

void options::init_defaults() {
	parse({
		L"--run", L"true",
		L"--output", L"@stdout"
	});
}
