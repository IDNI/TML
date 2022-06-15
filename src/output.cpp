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
#include "output.h"

using namespace std;

wostream wcnull(0);
ostream cnull(0);

const map<output::type_t, string> output::type_names_ = {
	{ NONE,   "@null"   },
	{ STDOUT, "@stdout" },
	{ STDERR, "@stderr" },
	{ BUFFER, "@buffer" },
	{ NAME,   "@name"   }
};
outputs* outputs::o_ = 0;

namespace o {
	void init_outputs(outputs& oo) {
		oo.create("output",               ".out.tml");
		oo.create("error",                ".error.log");
		oo.create("info",                 ".info.log");
		oo.create("debug",                ".debug.log");
		oo.create("dump",                 ".dump.tml");
		oo.create("benchmarks",           ".bench.log");
		oo.create("transformed",          ".trans.tml");
		oo.create("parser-benchmarks",    ".parser-bench.log");
		oo.create("parser-to-dot",        ".dot");
		oo.create("parser-to-tml",        ".parsed.tml");
		oo.create("parser-to-rules",      ".parsed-rules.tml");
		oo.create("program-gen",          ".cpp");
#ifdef WITH_THREADS
		oo.create("repl-output",          ".repl.out.log");
#endif
	}
	void use(outputs* oo) { oo->use(); }
	ostream_t& to(const string& n) { return outputs::to(n); }
	ostream_t& out()  { static auto& x = outputs::to("output"); return x; }
	ostream_t& err()  { static auto& x = outputs::to("error");  return x; }
	ostream_t& inf()  { static auto& x = outputs::to("info");   return x; }
	ostream_t& dbg()  { static auto& x = outputs::to("debug");  return x; }
#ifdef WITH_THREADS
	ostream_t& repl() { static auto& x = outputs::to("repl");   return x; }
#endif
	ostream_t& dump() { static auto& x = outputs::to("dump"); return x; }
	ostream_t& ms()   { static auto& x = outputs::to("benchmarks");
								return x; }
	ostream_t& pms()  { static auto& x = outputs::to("parser-benchmarks");
								return x; }
	ostream_t& transformed() { static auto& x = outputs::to("transformed");
								return x; }
	bool enabled(std::string n) { return outputs::enabled(n); }
}

output::type_t output::get_type(string t) {
	t = t == "" ? "@stdout" : t;
	for (auto& it : output::type_names_)
		if (it.second == t) return it.first;
	return FILE;
}

output::type_t output::target(const string t) {
	type_ = t == "" ? STDOUT : get_type(t);
	bool open_path_before_finish = false;
	switch (type_) {
		case NONE:                os(&CNULL);     break;
		case STDOUT:              os(&COUT); break;
		case STDERR:              os(&CERR); break;
		case BUFFER:
			buffer_.str(EMPTY_STRING); os(&buffer_); break;
		case NAME:
			{
				string name = outputs::named();
				if (!name.size())
					return o::err() << "output '"
					<< name_ << "' targeting @name without "
					"setting name" << endl,
					os(&CNULL), NONE;
				ostringstream ss; ss << name << ext_;
				path_ = ss.str();
			}
			open_path_before_finish = true;
			break;
		case FILE:
			path_ = t, open_path_before_finish = true;
			break;
		default: DBGFAIL;
	}
	if (open_path_before_finish)
		file_.open(path_, ofstream::binary | ofstream::app),
		//file_.imbue(locale("")),
		os(&file_);
	return type_;
}

bool outputs::add(sp_output out) {
	string n = out->name();
	auto it = find(ns_.begin(), ns_.end(), n);
	if (it != ns_.end()) {
		size_t i = std::distance(ns_.begin(), it);
		os_.at(i)->target(out->target()), out = os_.at(i);
	} else ns_.push_back(n), os_.push_back(out);
	//o_->update_pointers(n, out.get());
	return true;
}

ostream_t& outputs::to(const string& n) {
	output* o = get(n);
	if (o) return o->os();
	//DBGFAIL;
	return CNULL;
}

void outputs::target(const string& n, const string& t) {
	output* o = get(n);
	if (o) o->target(t);
	else {
		CERR << "target does not exist: " << n << endl;
		DBGFAIL;
	}
}
