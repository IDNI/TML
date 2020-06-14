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

extern std::wostream wcnull;

class output {
public:
	enum type_t { NONE, STDOUT, STDERR, FILE, BUFFER, NAME };
	output(std::wstring n, std::wstring t = L"", std::wstring e = L"")
		: os_(&wcnull), file_(), buffer_(L""),
		name_(n), ext_(e), path_(L""), type_(target(t)) { }
	std::wstring name() const { return name_; }
	std::wstring path() const { return path_; }
	type_t type() const { return type_; }
	std::wostream& os() { return *os_; }
	std::wstring target() const {
		return (type_ == FILE) ? path_ : type_name(type_); }
	type_t target(const std::wstring t);
	std::wstring read() {
		return type_ == BUFFER ? buffer_.str() : L""; }
	bool is_null() const { return type_ == NONE; }
	template <typename T>
	output& operator<<(const T& value) { *os_ << value; return *this; }
	static type_t get_type(std::wstring t);
	static std::wstring type_name(type_t t) { return type_names_.at(t); }
	static std::shared_ptr<output> create(std::wstring n,
		std::wstring t = L"", std::wstring e = L"") {
			return std::make_shared<output>(n, t, e); }
private:
	std::wostream* os_;          // output stream
	std::wofstream file_;        // file stream output
	std::wostringstream buffer_; // buffer stream output
	std::wstring name_;          // name of the output stream
	std::wstring ext_;           // filename extension
	std::wstring path_;          // file path
	type_t type_ = NONE;
	std::wostream& os(std::wostream* s) { os_ = s; return *os_; }
	static const std::map<type_t, std::wstring> type_names_;
};

using p_output   = output*;
using sp_output  = std::shared_ptr<output>;
using outputmap  = std::map<std::wstring, sp_output>;

class outputs : public outputmap {
public:
	outputs() : outputmap() { if (!o_) { o_ = this; init_defaults(); } }
	bool add(sp_output o);
	void use() { o_ = this; }
	void update_pointers(const std::wstring& n, output* o);
	void create(std::wstring n, std::wstring e, std::wstring t = L"@null") {
		add(output::create(n, t, e));
	}
	void init_defaults() {
		create(L"output",      L".out.tml");
		create(L"error",       L".error.log");
		create(L"info",        L".info.log");
		create(L"debug",       L".debug.log");
		create(L"dump",        L".dump.tml");
		create(L"benchmarks",  L".bench.log");
		create(L"transformed", L".trans.tml");
		create(L"repl-output", L".repl.out.log");
		create(L"xsb",         L".P");
		create(L"swipl",       L".pl");
		create(L"souffle",     L".souffle");
	}
	static outputs* in_use() { return o_; }
	static std::wostream& out()  { return o_to(o_->out_);  }
	static std::wostream& err()  { return o_to(o_->err_);  }
	static std::wostream& inf()  { return o_to(o_->inf_);  }
	static std::wostream& dbg()  { return o_to(o_->dbg_);  }
	static std::wostream& repl() { return o_to(o_->repl_); }
	static std::wostream& ms()   { return o_to(o_->ms_);   }
	static std::wostream& dump() { return o_to(o_->dump_); }
	static output* get(const std::wstring& n) { return o_->o_get(n); }
	static std::wostream& to(const std::wstring& n);
	static bool exists(const std::wstring& n) { return o_->o_exists(n); }
	static std::wstring read(const std::wstring& n) {return get(n)->read();}
	static void target(const std::wstring& n, const std::wstring& t);
	static void name(std::wstring n) { o_->name_ = n; }
	static std::wstring named() { return o_->name_; }
private:
	output *out_=0, *err_=0, *inf_=0, *dbg_=0, *repl_=0, *ms_=0, *dump_=0;
	std::wstring name_ = L"";
	static outputs* o_; // global outputs
	p_output o_get(std::wstring n) {
		auto it = find(n); return it != end() ? it->second.get() : 0; }
	bool o_exists(const std::wstring nam) { return find(nam) != end(); }
	static std::wostream& o_to(output* x) { return x ? x->os() : wcnull; }
};

namespace o { // o:: namespace shortcuts
	void init_defaults(outputs* oo);
	void use (outputs* oo);
	std::wostream& to(const std::wstring& n);
	std::wostream& out();
	std::wostream& err();
	std::wostream& inf();
	std::wostream& dbg();
	std::wostream& repl();
	std::wostream& ms();
	std::wostream& dump();
}

#endif
