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
#include "err.h"
#ifdef WITH_THREADS
#include "repl.h"
#endif
using namespace std;

//void print_memos_len();

int main(int argc, char** argv) {
	setlocale(LC_ALL, "");
	inputs ii;
	outputs oo;
	options o(argc, argv, &ii, &oo);
	//o.parse({ "-autotype" }, true);
	bdd::init(o.enabled("bdd-mmap") ? MMAP_WRITE : MMAP_NONE,
		o.get_int("bdd-max-size"), o.get_string("bdd-file"));
	// read from stdin by default if no -i(e), -h, -v and no -repl/udp
	if (o.disabled("i") && o.disabled("ie")
#ifdef WITH_THREADS
			&& o.disabled("repl") && o.disabled("udp")
#endif
			&& o.disabled("h") && o.disabled("v"))
		o.parse(strings{ "-i",  "@stdin" }, true);
#ifdef WITH_THREADS
	if (o.enabled("udp") && o.disabled("repl")) o.enable("repl");
	if (o.enabled("repl")) repl r(o);
	else {
#endif
		try {
			driver d(o);
			string archive_file = o.get_string("load");
			if (archive_file != "") d.load(archive_file);
			d.run((size_t)o.get_int("steps"),
				(size_t)o.get_int("break"),
				o.enabled("break-on-fp"));
			archive_file = o.get_string("save");
			if (archive_file != "") d.save(archive_file);
			if (o.enabled("dump") && d.result &&
				!d.out_goals(o::dump())) d.dump();
			if (o.enabled("dict")) d.out_dict(o::inf());
			if (o.enabled("csv")) d.save_csv();

		} catch (parse_error_exception &e) {
			o::err() << e.what() << endl;
		} catch (runtime_error_exception &e) {
			o::err() << e.what() << endl;
		}
#ifdef WITH_THREADS
	}
#endif
	onexit = true;
//	print_memos_len();
	return 0;
}
