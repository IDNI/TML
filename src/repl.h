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

class wistream_async_reader : public async_reader<std::wstring> {
public:
	wistream_async_reader(std::wistream* is) : async_reader(), is(is) { }
protected:
	std::wistream* is;
	void read_in_thread() {
		std::wstring l;
		while (std::getline(*is, l)) {
			std::lock_guard<std::mutex> lk(m);
			q.push(std::move(l));
		}
		eof = true;
	}
};

class repl {
	options& o;
	std::wostream& os;
	driver *d = 0;
	std::unique_ptr<udp> up_udp;
	wistream_async_reader wcin_reader{&std::wcin};
	bool fin = false;
	bool ar = false;  // auto run
	bool ap = true;   // auto print
	bool ai = false;  // auto info
	bool ps = false;  // print steps
	bool pu = false;  // print db updates each step
	bool cu = false;  // collect updates into tml_update relation
	bool ils = false; // input line sequencing: is each input line a newseq?

	void loop();
	bool eval_input(std::wostream& os, std::wstring &l);
	void prompt(std::wostream& os);
	void redrive(const std::wstring src = L"");

	void help(std::wostream& os) const;
	void print(std::wostream& os);
	void list(std::wostream& os, size_t p = 0);
	void restart(std::wostream& os);
	void reparse(std::wostream& os);
	void reset(std::wostream& os);
	void dump(std::wostream& os);
	void info(std::wostream& os);
	bool toggle(std::wostream& os, const std::wstring& name, bool &setting);
	void add(std::wostream& os, std::wstring line);
	void run(std::wostream& os, size_t steps = 0, size_t break_on_step=0,
		bool break_on_fp=0);
	void step(std::wostream& os, size_t steps = 1)    { run(os, steps); };
	void break_on_fp(std::wostream& os)               { run(os,0,0,true); };
	void break_on_step(std::wostream& os, size_t brs) { run(os, 0, brs); };

	// default os
	bool eval_input(std::wstring &l) { return eval_input(os, l); }
	void help() const { help(os); }
	void print() { print(os); }
	void list(size_t p = 0) { list(os, p); }
	void restart() { restart(os); }
	void reparse() { reparse(os); }
	void reset() { reset(os); }
	void dump();
	void info() { info(os); }
	bool toggle(const std::wstring& name, bool &setting) {
		return toggle(os, name, setting);
	}
	void add(std::wstring line) { add(os, line); }
	void run(size_t steps, size_t break_on_step = 0, bool break_on_fp = 0) {
		run(os, steps, break_on_step, break_on_fp);
	}
	void step(size_t steps = 1)                       { run(steps); };
	void break_on_fp()                                { run(0, 0, true); };
	void break_on_step(size_t brs)                    { run(0, brs); };
public:
	repl(options &o, std::wostream& os = o::repl());
};

#endif
