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
#include <memory>
#include "defs.h"

class output {
public:
	enum type_t { NONE, STDOUT, STDERR, FILE, BUFFER, NAME };
	output(const std::string n, const std::string t = "", std::string e = "")
		: os_(&CNULL), file_(), buffer_(),
		name_(n), ext_(e), path_(""), type_(target(t)) { }
	std::string name() const { return name_; }
	std::string path() const { return path_; }
	type_t type() const { return type_; }
	ostream_t& os() { return *os_; }
	std::string target() const {
		return (type_ == FILE) ? path_ : type_name(type_); }
	type_t target(const std::string t);
	sysstring_t read() {
		return type_ == BUFFER ? buffer_.str() : sysstring_t(); }
	void clear() { if (type_ == BUFFER) buffer_.str({}); }
	bool is_null() const { return type_ == NONE; }
	template <typename T>
	output& operator<<(const T& value) { *os_ << value; return *this; }
	static type_t get_type(std::string t);
	static std::string type_name(type_t t) { return type_names_.at(t); }
	static std::shared_ptr<output> create(std::string n,
		std::string t = "", std::string e = "") {
			return std::make_shared<output>(n, t, e); }
private:
	ostream_t* os_;          // output stream
	ofstream_t file_;        // file stream output
	ostringstream_t buffer_; // buffer stream output
	std::string name_;          // name of the output stream
	std::string ext_;           // filename extension
	std::string path_;          // file path
	type_t type_ = NONE;
	ostream_t& os(ostream_t* s) { os_ = s; return *os_; }
	static const std::map<type_t, std::string> type_names_;
};

using p_output   = output*;
using sp_output  = std::shared_ptr<output>;
using outputmap  = std::map<std::string, sp_output>;

class outputs : public outputmap {
public:
	outputs() : outputmap() { if (!o_) { o_ = this; init_defaults(); } }
	bool add(sp_output o);
	void use() { o_ = this; }
	void update_pointers(const std::string& n, output* o);
	void create(std::string n, std::string e, std::string t = "@null") {
		add(output::create(n, t, e));
	}
	void init_defaults() {
		create("output",      ".out.tml");
		create("error",       ".error.log");
		create("info",        ".info.log");
		create("debug",       ".debug.log");
		create("dump",        ".dump.tml");
		create("benchmarks",  ".bench.log");
		create("transformed", ".trans.tml");
#ifdef WITH_THREADS
		create("repl-output", ".repl.out.log");
#endif
		create("xsb",         ".P");
		create("swipl",       ".pl");
		create("souffle",     ".souffle");
	}
	static outputs* in_use() { return o_; }
	static ostream_t& out()  { return o_ ? o_to(o_->out_)  : CNULL; }
	static ostream_t& err()  { return o_ ? o_to(o_->err_)  : CNULL; }
	static ostream_t& inf()  { return o_ ? o_to(o_->inf_)  : CNULL; }
	static ostream_t& dbg()  { return o_ ? o_to(o_->dbg_)  : CNULL; }
#ifdef WITH_THREADS
	static ostream_t& repl() { return o_ ? o_to(o_->repl_) : CNULL; }
#endif
	static ostream_t& ms()   { return o_ ? o_to(o_->ms_)   : CNULL;   }
	static ostream_t& dump() { return o_ ? o_to(o_->dump_) : CNULL; }
	static output* get(const std::string& n) { return o_?o_->o_get(n):0; }
	static ostream_t& to(const std::string& n);
	static bool exists(const std::string& n) { return o_?o_->o_exists(n):0;}
	static sysstring_t read(const std::string& n) { return get(n)->read();}
	static void clear(const std::string& n) { get(n)->clear(); }
	static void target(const std::string& n, const std::string& t);
	static void name(std::string n) { if (o_) o_->name_ = n; }
	static std::string named() { return o_?o_->name_:std::string(); }
private:
	output *out_=0, *err_=0, *inf_=0, *dbg_=0, *ms_=0, *dump_=0;
#ifdef WITH_THREADS
	output *repl_=0;
#endif
	std::string name_ = "";
	static outputs* o_; // global outputs
	p_output o_get(std::string n) {
		auto it = find(n); return it != end() ? it->second.get() : 0; }
	bool o_exists(const std::string nam) { return find(nam) != end(); }
	static ostream_t& o_to(output* x) { return x ? x->os() : CNULL; }
};

namespace o { // o:: namespace shortcuts
	void init_defaults(outputs* oo);
	void use (outputs* oo);
	ostream_t& to(const std::string& n);
	ostream_t& out();
	ostream_t& err();
	ostream_t& inf();
	ostream_t& dbg();
#ifdef WITH_THREADS
	ostream_t& repl();
#endif
	ostream_t& ms();
	ostream_t& dump();
}

template <typename T, typename T1, typename T2>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::map<T1,T2>& m);

template<typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const env& e);

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const vbools& x);

#endif
