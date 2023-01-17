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
#ifndef __REPL_H__
#define __REPL_H__
#include "driver.h"
#include "udp.h"
#include "async_reader.h"

namespace idni {

class istream_async_reader : public async_reader<sysstring_t> {
public:
	istream_async_reader(istream_t* is) : async_reader(), is(is) { }
protected:
	istream_t* is;
	void read_in_thread() {
		sysstring_t l;
		while (std::getline(*is, l)) {
			std::lock_guard<std::mutex> lk(m);
			q.push(std::move(l));
		}
		eof = true;
	}
};

class repl {
public:
	repl(options &o, ostream_t& os = o::repl());
private:
	options& o;
	ostream_t& os;
	std::unique_ptr<driver> d = 0;
	std::unique_ptr<udp> up_udp;
	istream_async_reader in_reader{&CIN};
	bool fin = false;
	bool ar = true;   // auto run
	bool ap = true;   // auto print
	bool ai = false;  // auto info
	bool ps = false;  // print steps
	bool pu = false;  // print db updates each step
	bool cu = false;  // collect updates into tml_update relation
	bool ils = false; // input line sequencing: is each input line a newseq?

	void loop();
	template <typename T>
	bool eval_input(std::basic_ostream<T>&, std::string l);
	template <typename T>
	void prompt(std::basic_ostream<T>&);
	void redrive(const std::string& src);

	template <typename T>
	void help(std::basic_ostream<T>&) const;
	template <typename T>
	void print(std::basic_ostream<T>&);
	template <typename T>
	void list(std::basic_ostream<T>&, size_t p = 0);
	template <typename T>
	void restart(std::basic_ostream<T>&);
	template <typename T>
	void reparse(std::basic_ostream<T>&);
	template <typename T>
	void reset(std::basic_ostream<T>&);
	template <typename T>
	void dump(std::basic_ostream<T>&);
	template <typename T>
	void info(std::basic_ostream<T>&);
	template <typename T>
	bool toggle(std::basic_ostream<T>&, const std::string& name,
		bool &setting);
	template <typename T>
	void add(std::basic_ostream<T>&, std::string line);
	template <typename T>
	void run(std::basic_ostream<T>&, size_t steps=0,size_t break_on_step=0);
	template <typename T>
	void step(std::basic_ostream<T>&, size_t steps = 1)   { run(os, steps);}
	template <typename T>
	void break_on_step(std::basic_ostream<T>&, size_t brs){ run(os,0, brs);}
	void out_dict(std::wostream& os);
	void out_dict(std::ostream& os);
	bool eval_input(const std::string &l) { return eval_input(os, l); }
	void help() const { help(os); }
	void print() { print(os); }
	void list(size_t p = 0) { list(os, p); }
	void restart() { restart(os); }
	void reparse() { reparse(os); }
	void reset() { reset(os); }
	void dump();
	void info() { info(os); }
	bool toggle(const std::string& name, bool &setting) {
		return toggle(os, name, setting);
	}
	void add(const std::string& line) { add(os, line); }
	void run(size_t steps, size_t break_on_step = 0) {
		run(os, steps, break_on_step);
	}
	void step(size_t steps = 1)                       { run(steps); };
	void break_on_step(size_t brs)                    { run(0, brs); };
};

} // idni namespace
#endif
