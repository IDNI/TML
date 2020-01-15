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
#include "repl.h"
using namespace std;

//void print_memos_len();

int main(int argc, char** argv) {
	setlocale(LC_ALL, "");
	driver::init();
	options o(argc, argv);
	// read from stdin by default if no -i(e), -h, -v and no -repl
	if (o.disabled(L"i") && o.disabled(L"ie") && o.disabled(L"repl")
				&& o.disabled(L"h") && o.disabled(L"v"))
		o.parse(wstrings{ L"-i",  L"@stdin" }, true);
	if (o.enabled(L"repl")) repl r(o);
	else {
		driver d(o);
		d.run();
		//DBG(d.info(o::dbg()<<endl); o::dbg()<<endl;)
		NDBG(if (o.enabled(L"dump") && d.result)
			d.out(output::to(L"dump"));)
		if (o.enabled(L"csv")) d.save_csv();
	}
	onexit = true;
//	print_memos_len();
	return 0;
}
