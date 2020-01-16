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
#include <sstream>
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

void options::parse(int c, char** v, bool internal) {
	wstrings wargs = {};
	for (int i = 0; i < c; ++i)
		wargs.push_back(s2ws(string(v[i])));
	parse(wargs, internal);
}

void options::parse(strings sargs, bool internal) {
	wstrings wargs = {};
	for (size_t i=0; i < sargs.size(); ++i) wargs.push_back(s2ws(sargs[i]));
	parse(wargs, internal);
}

void options::parse(wstrings wargs, bool internal) {
	wstring v;
	bool skip_next = false;
	for (size_t i = 0; i < wargs.size(); ++i) {
		if (!internal) args.push_back(wargs[i]);
		if (skip_next) skip_next = false;
		else skip_next = parse_option(wargs, i);
	}
}

bool options::enabled(const wstring &name) const {
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

bool options::is_value(const wstrings &wargs, const size_t &i) {
	if (i >= wargs.size()) return false;
	else return wargs[i] == L"-" ||
			(wargs[i].rfind(L"---", 0) == 0) ||
			wargs[i][0] != L'-';
}

bool options::parse_option(const wstrings &wargs, const size_t &i) {
	option o;
	bool disabled = false;
	bool skip_next = false;
	size_t pos = 0;
	const wstring &arg = wargs[i];
	//DBG(o::out()<<L"parse_option: "<<arg<<L' '<<i<<endl;)
	// skip hyphens
	while (pos < arg.length() && arg[pos] == L'-' && pos < 2) ++pos;
	wstring a = arg.substr(pos);
	// is option disabled?
	if (a.rfind(L"disable-",   0) == 0) disabled = true, a = a.substr(8);
	else if (a.rfind(L"dont-", 0) == 0) disabled = true, a = a.substr(5);
	else if (a.rfind(L"no-",   0) == 0) disabled = true, a = a.substr(3);
	if (!get(a, o)) {
		if (!i) goto done; // arg[0] is not expected to be an argument
		o::err() << L"Unknown argument: " << wargs[i]<<endl;
		return is_value(wargs, i+1);
	}
	if (disabled) o.disable();
	else if (is_value(wargs, i+1))
		o.parse_value(wargs[i+1]),
		skip_next = true;
	else o.parse_value(L"");
	set(o.name(), o);
done:
	return skip_next;
}

#define add_bool(n,desc) add(option(option::type::BOOL, {n}).description(desc))
#define add_output(n,desc) add(option(option::type::STRING, {n}, \
		[](const option::value& v) { \
			output::set_target(n,v.get_string()); \
		}).description((desc)))
#define add_output_alt(n,alt,desc) add(option(option::type::STRING, {n, alt}, \
		[](const option::value& v) { \
			output::set_target(n,v.get_string()); \
		}).description((desc)))

void options::setup() {

	add(option(option::type::BOOL, { L"help", L"h", L"?" },
		[this](const option::value& v) {
			if (v.get_bool()) help(o::inf());
		})
		.description(L"this help"));
	add(option(option::type::BOOL, { L"version", L"v" },
		[](const option::value& v) {
			if (v.get_bool()) o::inf() << L"TML: "
				<< GIT_DESCRIBED << endl;
			DBG(if (v.get_bool()) o::inf()
				<< L"commit: " << GIT_COMMIT_HASH << L" ("
				<< GIT_BRANCH << L')' <<endl;)
		})
		.description(L"this help"));
	add(option(option::type::STRING, {L"input", L"i"},
		[this](const option::value& v) {
			wstringstream is;
			if (v.get_string()==L"@stdin" || v.get_string()==L"-")
				is << wcin.rdbuf();
			else {
				wifstream f(ws2s(v.get_string()));
				if (f.good()) is << f.rdbuf();
				else o::err()
					<< L"Error while opening file: "
					<< v.get_string() << endl;
			}
			add_input_data(is.str());
		}).description(L"input           (@stdin by default)"));
	add(option(option::type::STRING, {L"input-eval", L"ie"},
		[this](const option::value& v) {
			add_input_data(v.get_string());
		}).description(L"input string to evaluate"));
	add_bool(L"sdt",     L"sdt transformation");
	add_bool(L"bin",     L"bin transformation");
	add_bool(L"proof",   L"extract proof");
	add_bool(L"repl",    L"run TML in REPL mode");
	add_bool(L"run",     L"run program     (enabled by default)");
	add_bool(L"csv",     L"save result into CSV files");
	add_bool(L"optimize",L"optimize and show more benchmarks");
	add(option(option::type::STRING, { L"name", L"n" },
		[](const option::value& v) {
			output::set_name(v.get_string());
		})
		.description(L"name used for @name output"));
	add_output    (L"dump",        L"dump output     (@stdout by default)");
	add_output_alt(L"output", L"o",L"standard output (@stdout by default)");
	add_output    (L"error",       L"errors          (@stderr by default)");
	add_output    (L"info",        L"info            (@stderr by default)");
	add_output    (L"debug",       L"debug output");
	add_output    (L"benchmarks",  L"benchmarking results");
	add_output_alt(L"transformed", L"t",  L"transformation into clauses");
	add_output    (L"repl-output", L"repl output");
	add_output(L"xsb",     L"attempt to translate program into XSB");
	add_output(L"swipl",   L"attempt to translate program into SWI-Prolog");
	add_output(L"souffle", L"attempt to translate program into Souffle");

	init_defaults();
}

#undef add_bool
#undef add_output
#undef add_output_alt

void options::init_defaults() {
	parse({
		L"--run",
		L"--output",      L"@stdout",
		L"--dump",        L"@stdout",
		L"--error",       L"@stderr",
		L"--info",        L"@stderr",
		L"--repl-output", L"@stdout",
		L"--benchmarks",  L"@stdout",
		L"--optimize"
	}, true);
	DBG(parse(wstrings{ L"--debug", L"@stderr" }, true);)
}

void options::help(wostream& os) const {
	os<<L"Usage:"<<endl;
	os<<L"\ttml [options]"<<endl;
	os<<endl;
	os<<L"options:"<<endl;
	os<<L"\tOptions are preceded by one or two hyphens (--run/-run)."<<endl;
	os<<L"\tDisable option by prefixing it with disable-, no- or dont-"
		<<endl;
	os<<L"\t\t(--disable-run/--no-run/--dont-run)."<<endl;
	os<<endl;
	for (auto oit : opts) oit.second.help(os)<<endl;
	os<<endl;
	os<<L"bool:"<<endl;
	os<<L"\tEnabled if 'true', 't', '1', 'yes', 'on', 'enabled' or "
		<<L"if no argument."<<endl;
	os<<endl;
	os<<L"input:"<<endl;
	os<<L"\t[FILENAME | @stdin | - ]"<<endl;
	os<<endl;
	os<<L"\t@stdin (or -) reads input from stdin"<<endl;
	os<<L"\tFILENAME inputs can be used more than once to concatenate "
		<<L"multiple files"<<endl;
	os<<L"\t--input can be combined with --input-eval too"<<endl;
	os<<endl;
	os<<L"output:"<<endl;
	os<<L"\t[FILENAME | @stdout | @stderr | @name | @null | @buffer]"<<endl;
	os<<endl;
	os<<L"\t@null\tdisable output"<<endl;
	os<<L"\t@stdout\tredirect to stdout"<<endl;
	os<<L"\t@stderr\tredirect to stderr"<<endl;
	os<<L"\t@buffer\tredirect to buffer to be read through API later"<<endl;
	os<<L"\t@name\tredirect to a file named by --name (ext predefined)"
		<<endl;
}
