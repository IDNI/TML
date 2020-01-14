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

class repl {
	options& o;
	std::wostream& os;
	driver *d = 0;
	bool fin = false;
	bool ar = false;  // auto run
	bool ap = true;   // auto print
	bool ai = false;  // auto info
	bool ils = false; // input line sequencing: is each input line a newseq?
	void help() const;
	void redrive(const std::wstring src = L"");
	void run(size_t steps = 0, size_t break_on_step=0, bool break_on_fp=0);
	void step(size_t steps = 1)    { run(steps); };
	void break_on_fp()             { run(0, 0, true); };
	void break_on_step(size_t brs) { run(0, brs); };
	void loop();
	void print();
	void list(size_t p = 0);
	void restart();
	void reparse();
	void reset();
	void dump();
	void info();
	void toggle(const std::wstring& name, bool &setting);
	void add(std::wstring line);
public:
	repl(options &o, std::wostream& os = o::repl());
};

#endif
