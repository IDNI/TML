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
#ifdef WITH_THREADS
#include "repl.h"
#endif
using namespace std;

//void print_memos_len();

int main(int argc, char** argv) {
	setlocale(LC_ALL, "");
	outputs oo;
	options o(argc, argv, &oo);
	bdd::init();
	// read from stdin by default if no -i(e), -h, -v and no -repl/udp
	if (o.disabled(L"i") && o.disabled(L"ie")
#ifdef WITH_THREADS
			&& o.disabled(L"repl") && o.disabled(L"udp")
#endif
			&& o.disabled(L"h") && o.disabled(L"v"))
		o.parse(wstrings{ L"-i",  L"@stdin" }, true);
#ifdef WITH_THREADS
	if (o.enabled(L"udp") && o.disabled(L"repl")) o.enable(L"repl");
	if (o.enabled(L"repl")) repl r(o);
	else {
#endif
		driver d(o);
		d.run((size_t)o.get_int(L"steps"),
			(size_t)o.get_int(L"break"),
			o.enabled(L"break-on-fp"));
		if (o.enabled(L"dump") && d.result &&
			!d.out_goals(o::dump())) d.dump();
		if (o.enabled(L"dict")) d.out_dict(o::inf());
		if (o.enabled(L"csv")) d.save_csv();
#ifdef WITH_THREADS
	}
#endif
	onexit = true;
//	print_memos_len();
	return 0;
}
