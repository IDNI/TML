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

bool options::get(const string name, option& o) const {
	auto ait = alts.find(name);        if (ait == alts.end()) return false;
	auto oit = opts.find(ait->second); if (oit == opts.end()) return false;
	return o = oit->second, true;
}

int options::get_int(string name) const {
	option o; return get(name, o) ? o.get_int() : 0;
}

bool options::get_bool(string name) const {
	option o; return get(name, o) ? o.get_bool() : false;
}

string options::get_string(string name) const {
	option o; return get(name, o) ? o.get_string() : "";
}

void options::parse(int c, char** v, bool internal) {
	strings sargs = {};
	for (int i = 0; i < c; ++i)
		sargs.push_back(string(v[i]));
	parse(sargs, internal);
}

void options::parse(wstrings wargs, bool internal) {
	strings sargs;
	for (size_t i=0; i < wargs.size(); ++i) sargs.push_back(ws2s(wargs[i]));
	parse(sargs, internal);
}

void options::parse(strings sargs, bool internal) {
	string v;
	bool skip_next = false;
	for (size_t i = 0; i < sargs.size(); ++i) {
		if (!internal) args.push_back(sargs[i]);
		if (skip_next) skip_next = false;
		else skip_next = parse_option(sargs, i);
	}
}

template <typename T>
void options::set(const string &name, T val) {
	option o;
	if (!get(name, o)) return;
	o.v.set(val);
	set(name, o);
}
template void options::set<int_t>(const std::string&, int_t);
template void options::set<std::string>(const std::string&, std::string);

void options::enable (const string &name) { set(name, true ); }
void options::disable(const string &name) { set(name, false); }

bool options::enabled(const string &name) const {
	option o;
	if (!get(name, o)) return false;
	switch (o.get_type()) {
		case option::type::BOOL:   return o.get_bool();
		case option::type::INT:    return o.get_int() > 0;
		case option::type::STRING: {
			output* t = outputs::get(o.name());
			return t ? !t->is_null() : o.get_string() != "";
		}
		default: ;
	}
	return false;
}

bool options::is_value(const strings &sargs, const size_t &i) {
	if (i >= sargs.size()) return false;
	else return sargs[i] == "-" ||
			(sargs[i].rfind("---", 0) == 0) ||
			sargs[i][0] != '-';
}

bool options::parse_option(const strings &sargs, const size_t &i) {
	option o;
	bool disabled = false;
	bool skip_next = false;
	size_t pos = 0;
	const string &arg = sargs[i];
	//DBG(o::out()<<"parse_option: "<<arg<<' '<<i<<endl;)
	// skip hyphens
	while (pos < arg.length() && arg[pos] == '-' && pos < 2) ++pos;
	string a = arg.substr(pos);
	// is option disabled?
	if (a.rfind("disable-",   0) == 0) disabled = true, a = a.substr(8);
	else if (a.rfind("dont-", 0) == 0) disabled = true, a = a.substr(5);
	else if (a.rfind("no-",   0) == 0) disabled = true, a = a.substr(3);
	if (!get(a, o)) {
		if (!i) goto done; // arg[0] is not expected to be an argument
		o::err() << "Unknown argument: " << sargs[i]<<endl;
		return is_value(sargs, i+1);
	}
	if (disabled) o.disable();
	else if (is_value(sargs, i+1))
		o.parse_value(sargs[i+1]),
		skip_next = true;
	else o.parse_value("");
	set(o.name(), o);
done:
	return skip_next;
}

#define add_bool(n,desc) add(option(option::type::BOOL, {n}).description(desc))
#define add_bool2(n1,n2,desc) add(option(option::type::BOOL, \
		{(n1),(n2)}).description(desc))
#define add_output(n,desc) add(option(option::type::STRING, {n}, \
		[this](const option::value& v) { \
			oo->target(n, v.get_string()); \
		}).description((desc)))
#define add_output_alt(n,alt,desc) add(option(option::type::STRING, {n, alt}, \
		[this](const option::value& v) { \
			oo->target(n, v.get_string()); \
		}).description((desc)))

void options::setup() {
	add(option(option::type::BOOL, { "help", "h", "?" },
		[this](const option::value& v) {
			if (v.get_bool()) help(o::out());
		})
		.description("this help"));
	add(option(option::type::BOOL, { "version", "v" },
		[](const option::value& v) {
			if (v.get_bool()) o::out() << "TML: "
				<< GIT_DESCRIBED << endl;
			DBG(if (v.get_bool()) o::out()
				<< "commit: " << GIT_COMMIT_HASH << " ("
				<< GIT_BRANCH << ')' <<endl;)
		})
		.description("this help"));
	add(option(option::type::STRING, { "input", "i" },
		[this](const option::value& v) {
			if (v.get_string() == "@stdin" || v.get_string() == "-")
				ii->add_stdin();
			else ii->add_file(v.get_string());
		}).description("input           (@stdin by default)"));
	add(option(option::type::STRING, { "input-eval", "ie" },
		[this](const option::value& v) {
			ii->add_string(v.get_string());
			//COUT << "inputs.size now: " << ii->size()
			//	<< " this: " << this << std::endl;
		}).description("input string to evaluate"));
#ifdef WITH_THREADS
	add_bool("udp",     "open REPL on udp socket");
	add(option(option::type::STRING, {"udp-addr", "ua"})
		.description("IP address (udp)"));
	add(option(option::type::INT, { "udp-port", "up" })
		.description("port (udp)"));
	add_bool("repl",    "run TML in REPL mode");
	add_output    ("repl-output", "repl output");
#endif
	add_bool("sdt",     "sdt transformation");
	add_bool("bin",     "bin transformation");
	add_bool("proof",   "extract proof");
	add_bool("run",     "run program     (enabled by default)");
	add_bool("csv",     "save result into CSV files");

	add_bool("bdd-mmap","use memory mapping for BDD database");
	add(option(option::type::INT, { "bdd-max-size" }).description(
		"Maximum size of a bdd memory map (default: 128 MB)"));
	add(option(option::type::STRING, { "bdd-file" })
		.description("Memory map file used for BDD database"));

	add(option(option::type::INT, { "steps", "s" })
		.description("run N steps"));
	add(option(option::type::INT, { "break", "b" })
		.description("break on the N-th step"));
	add(option(option::type::INT, { "regex-level", "" })
		.description("aggressive matching with regex with levels 1 and more." 
		"\n\t 1 - try all substrings - n+1  delete n rules after processing reg matching"));
	add_bool2("break-on-fp", "bfp", "break on a fixed point");

	add_bool2("populate-tml_update", "tml_update",
		"populates relation tml_update(N_step add|delete fact).");
	add_bool2("print-steps", "ps", "print steps");
	add_bool2("print-updates", "pu", "print updates");
	add_bool2("print-dict", "dict", "print internal string dictionary");
	add_bool2("reg-match", "regex", "applies regular expression matching");
	add_bool2("fp-step", "fp", "adds __fp__ fact when reaches a fixed point");
	add(option(option::type::BOOL, { "guards", "g", "unnest" },
		[this](const option::value& v) {
			if (v.get_bool()) this->enable("fp-step");
		}
	).description("transforms nested progs (req. for if and while)"));
	add_bool2("bitprog", "bpg", "transforms and prints rule in bit universe 2");
	add_bool("optimize","optimize and show more benchmarks");
	add(option(option::type::STRING, { "name", "n" },
		[](const option::value& v) {
			outputs::name(v.get_string());
		}).description("name used for @name output"));
	add(option(option::type::STRING, { "load", "l" })
		.description("load database from file before start"));
	add(option(option::type::STRING, { "save", "s" })
		.description("save database to file after finish"));
	add_output    ("dump",        "dump output     (@stdout by default)");
	add_output_alt("output", "o","standard output (@stdout by default)");
	add_output    ("error",       "errors          (@stderr by default)");
	add_output    ("info",        "info            (@null by default)");
	add_output    ("debug",       "debug output");
	add_output    ("benchmarks",  "benchmarking results (@null by default)");
	add_output_alt("transformed", "t",  "transformation into clauses");
	add_output("xsb",     "attempt to translate program into XSB");
	add_output("swipl",   "attempt to translate program into SWI-Prolog");
	add_output("souffle", "attempt to translate program into Souffle");

	init_defaults();
}

#undef add_bool
#undef add_bool2
#undef add_output
#undef add_output_alt

void options::init_defaults() {
	parse(strings{
		"--run",
		"--output",      "@stdout",
		"--dump",        "@stdout",
		"--error",       "@stderr",
#ifdef DEBUG
		"--info",        "@stderr",
		"--benchmarks",  "@stderr",
#endif
		"--optimize",
		"--bdd-max-size","134217728", // 128 MB
#ifdef WITH_THREADS
		"--repl-output", "@stdout",
		"--udp-addr",    "127.0.0.1",
		"--udp-port",    "6283"
#endif
	}, true);
	DBG(parse(strings{ "--debug", "@stderr" }, true);)
}

template <typename T>
void options::help(std::basic_ostream<T>& os) const {
	os<<"Usage:\n";
	os<<"\ttml [options]\n";
	os<<"\n";
	os<<"options:\n";
	os<<"\tOptions are preceded by one or two hyphens (--run/-run).\n";
	os<<"\tDisable option by prefixing it with disable-, no- or dont-\n";
	os<<"\t\t(--disable-run/--no-run/--dont-run).\n";
	os<<"\n";
	for (auto oit : opts) oit.second.help(os)<<"\n";
	os<<"\n";
	os<<"bool:\n";
	os<<"\tEnabled if 'true', 't', '1', 'yes', 'on', 'enabled' or "
		<<"if no argument.\n";
	os<<"\n";
	os<<"input:\n";
	os<<"\t[FILENAME | @stdin | - ]\n";
	os<<"\n";
	os<<"\t@stdin (or -) reads input from stdin\n";
	os<<"\tFILENAME inputs can be used more than once to concatenate "
		<<"multiple files\n";
	os<<"\t--input can be combined with --input-eval too\n";
	os<<"\n";
	os<<"output:\n";
	os<<"\t[FILENAME | @stdout | @stderr | @name | @null | @buffer]\n";
	os<<"\n";
	os<<"\t@null\tdisable output\n";
	os<<"\t@stdout\tredirect to stdout\n";
	os<<"\t@stderr\tredirect to stderr\n";
	os<<"\t@buffer\tredirect to buffer to be read through API later\n";
	os<<"\t@name\tredirect to a file named by --name (ext predefined)\n";
}
