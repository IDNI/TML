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
#include <cstring>
#include <iostream>
#ifdef __unix__
#include <sys/ioctl.h>
#endif
#include "driver.h"
using namespace std;

//void print_memos_len();

void repl(driver &d) {
	wstring line;
	while (wcin) {
		o::repl() << endl << L"TML> ";
		getline(wcin, line);
		d.run(raw_progs(line));
	}
}

int main(int argc, char** argv) {
	setlocale(LC_ALL, "");
	bdd::init();
	driver::init();
	options o(argc, argv);
	if (o.disabled(L"i") && o.disabled(L"ie") && o.disabled(L"repl")
				&& o.disabled(L"h") && o.disabled(L"v"))
		// read from stdin by default if no -i, -h, -v and no -repl
		o.parse(wstrings{ L"-i",  L"@stdin" }, true);
	driver d(o);
	if (o.enabled(L"repl")) repl(d);
	onexit = true;
//	print_memos_len();
	return 0;
}
