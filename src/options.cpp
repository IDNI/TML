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
#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#endif

using namespace std;

void options::add(option o) {
	set(o.name(), o);
	for (auto n : o.names()) alts[n] = o.name();
}

optional<option> options::get(const string name) const {
	if (auto ait = alts.find(name); ait == alts.end()) return nullopt;
	else if (auto oit = opts.find(ait->second); oit == opts.end())
		return nullopt;
	else return oit->second;
}

int options::get_int(string name) const {
	if(auto o = get(name)) return o->get_int(); else return 0;
}

bool options::get_bool(string name) const {
	if(auto o = get(name)) return o->get_bool(); else return false;
}

string options::get_string(string name) const {
	if(auto o = get(name)) return o->get_string(); else return "";
}

bool options::parse(int c, char** v, bool internal) {
	strings sargs = {};
	for (int i = 0; i < c; ++i) sargs.push_back(string(v[i]));
	return parse(sargs, internal);
}

bool options::parse(wstrings wargs, bool internal) {
	strings sargs;
	for (size_t i=0; i < wargs.size(); ++i) sargs.push_back(ws2s(wargs[i]));
	return parse(sargs, internal);
}

bool options::parse(strings sargs, bool internal) {
	string v;
	bool skip_next = false;
	for (size_t i = 0; i < sargs.size(); ++i) {
		if (!internal) args.push_back(sargs[i]);
		if (program_arguments) pargs.push_back(sargs[i]);
		else if (skip_next) skip_next = false;
		else if (!parse_option(sargs, i, skip_next))
			return false;
	}
	return true;
}

template <typename T>
void options::set(const string &name, T val) {
	if (auto o = get(name)) {
		o->v.set(val);
		set(name, *o);
	}
}
template void options::set<int_t>(const std::string&, int_t);
template void options::set<std::string>(const std::string&, std::string);

void options::enable (const string &name) { set(name, true ); }
void options::disable(const string &name) { set(name, false); }

bool options::enabled(const string &name) const {
	if (auto o = get(name)) {
		switch (o->get_type()) {
			case option::type::BOOL:   return o->get_bool();
			case option::type::INT:    return o->get_int() > 0;
			case option::type::STRING: {
				output* t = outputs::get(o->name());
				return t ? !t->is_null() : o->get_string()!="";
			}
			default: ;
		}
	}
	return false;
}

bool options::is_value(const strings &sargs, const size_t &i) {
	if (i >= sargs.size()) return false;
	else return sargs[i] == "-" ||
			(sargs[i].rfind("---", 0) == 0) ||
			sargs[i][0] != '-';
}

bool options::parse_option(const strings &sargs, const size_t &i,
	bool& skip_next)
{
	bool disabled = false;
	skip_next = false;
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
	if (auto o = get(a)) {
		if (disabled) o->disable();
		else if (is_value(sargs, i+1))
			o->parse_value(sargs[i+1]),
			skip_next = true;
		else o->parse_value("");
		set(o->name(), *o);
		return true;
	} else {
		if (!i) return true; // arg[0] is not expected to be an argument
		o::err() << "Unknown argument: " << sargs[i]<<endl;
		skip_next = is_value(sargs, i+1);
		return false;
	}
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
	add_bool("qc-subsume-z3",
		"Enable CQNC subsumption optimization using theorem prover Z3");
	add_bool("show-hidden", "show the contents of hidden relations");
	add_bool("split-rules",
		"transformation to reduce number of conjunctions in each rule");
	add_bool("cqc-subsume",
		"subsume queries into each other using CQC test");
	add_bool("cqnc-subsume",
		"subsume queries into each other using CQNC test");
	add_bool("cqc-factor",
		"factor out parts of queries using CQC test");
	add_bool("to-dnf",
		"convert FOL formulas into to DNF before running program");
	add_bool("O0",
		"enables optimization on requested transformations");
	add_bool("O1",
		"enables split-rules");
	add_bool("O2",
		"enables all O1 optimizations and also cqc-subsumes and cqnc-subsumes");
	add(option(option::type::INT, { "O3" })
		.description("enables all O2 optimizations and transforms the program into one where each step is equivalent to 2^x of the original's (default: x=0)"));
	add(option(option::type::INT, { "iterate" })
		.description("transforms the program into one where each step is equivalent to 2^x of the original's (default: x=0)"));
	add_bool("safecheck", "to be DEPRECATED: safety check will be always on");
	add(option(option::type::INT, { "iterate" }).description("transforms"
		" the program into one where each step is equivalent to 2^x of"
		" the original's (default: x=0)"));
	add_bool("gc",      "enable garbage collection");
	add(option(option::type::ENUM, { "proof" }, { "none", "tree", "forest", 
		"partial-tree", "partial-forest" }).description("control if and"
		" how proofs are extracted: none (default), tree, forest,"
		" partial-tree, partial-forest"));
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
		.description("aggressive matching with regex with levels 1 and"
		" more.\n\t 1 - try all substrings - n+1  delete n rules after"
		" processing reg matching"));
	add_bool2("break-on-fp", "bfp", "break on a fixed point");

	add_bool2("populate-tml_update", "tml_update",
		"populates relation tml_update(N_step add|delete fact).");
	add_bool2("print-steps", "ps", "print steps");
	add_bool2("print-updates", "pu", "print updates");
	add(option(option::type::STRING, { "print-updates-if", "pui" },
		[this](const option::value& v) {
			set("print-updates", true);
			pu_states.insert(v.get_string());
		}).description("active state to printing updates"));
	add_bool2("print-dict", "dict", "print internal string dictionary");

	add_bool("strgrammar", "...");

	add_bool2("reg-match", "regex", "applies regular expression matching");
	add_bool2("fp-step","fp","adds __fp__ fact when reaches a fixed point");
	add(option(option::type::STRING, {"arguments","args","options","opts"},
		[this](const option::value&) {
			this->program_arguments = !this->program_arguments;
		}
	 ).description("delimiter between TML and program's arguments"));
	add(option(option::type::BOOL, { "guards", "g", "unnest" },
		[this](const option::value& v) {
			if (v.get_bool()) this->enable("fp-step");
		}
	).description("transforms nested progs (req. for if and while)"));
	add_bool2("state-blocks", "sb", "transforms state blocks");

	add(option(option::type::INT, { "bitorder", "bod" })
		.description("specifies the variable ordering permutation"
							" (default: 0)"));
	add(option(option::type::BOOL, { "optimize" },
		[this](const option::value& v) {
			if (v.get_bool()) set("print-steps", true);
		})
		.description("optimize and show more benchmarks"));
	add(option(option::type::STRING, { "name", "n" },
		[](const option::value& v) {
			outputs::name(v.get_string());
		}).description("name used for @name output"));
	//add(option(option::type::STRING, { "load", "l" })
	//	.description("load database from file before start"));
	//add(option(option::type::STRING, { "save", "s" })
	//	.description("save database to file after finish"));
	add_bool2("earley", "ep", "use earley parser");
	add_bool2("print-ambiguity", "pamb", "print parsed ambiguous packs");
	add_bool2("print-traversing", "ptrv", "print parsed nodes traversed");
	add_bool2("bin-lr", "blr", "on the fly binarization and left "
					"right optimization for earley items");
	add_bool2("incr-gen-forest", "igf", "incremental generation of forest");
	add_output    ("dump",        "dump output     (@stdout by default)");
	add_output_alt("output", "o","standard output (@stdout by default)");
	add_output    ("error",       "errors          (@stderr by default)");
	add_output    ("info",        "info            (@null by default)");
	add_output    ("debug",       "debug output");
	add_output    ("benchmarks", "benchmarking results (@null by default)");
	add_output_alt("transformed", "t",  "transformation into clauses");
	add_output_alt("parser-benchmarks", "pms",  "parser benchmarking");
	add_output_alt("parser-to-dot",  "pdot", "parsed forest in dot format");
	add_output_alt("parser-to-tml",  "ptml", "parsed forest as tml facts");
	add_output_alt("parser-to-rules","prules","parsed forest as tml rules");
	add_output_alt("program-gen", "cpp",
		"generated C++ code of the given TML code");

#ifdef __EMSCRIPTEN__
#ifdef NODEFSMOUNT
#ifndef NODERAWFS
	static bool nodefsmounted = false;
	if (!nodefsmounted) {
		nodefsmounted = true;
		EM_ASM({
    			var directory = '/workspace';
    			FS.mkdir(directory);
    			FS.mount(NODEFS, {root : '.'}, directory);
			FS.chdir(directory);
		}, "fs");
	}
#endif
#endif
#endif

	init_defaults();
}

#undef add_bool
#undef add_bool2
#undef add_output
#undef add_output_alt

void options::init_defaults() {
	error |= !parse(strings{
		"--run",
		"--gc",
		"--proof",       "none",
		"--output",      "@stdout",
		"--dump",        "@stdout",
		"--error",       "@stderr",
#ifdef DEBUG
		"--info",        "@stderr",
		"--benchmarks",  "@stderr",
#endif
		"--optimize",
		"--bdd-max-size","134217728", // 128 MB
		"--safecheck",
#ifdef WITH_THREADS
		"--repl-output", "@stdout",
		"--udp-addr",    "127.0.0.1",
		"--udp-port",    "6283"
#endif
	}, true);
	DBG(error |= !parse(strings{ "--debug", "@stderr" }, true);)
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
