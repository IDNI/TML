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

int main(int argc, char** argv) {
	setlocale(LC_ALL, "");
	inputs ii;
	outputs oo;
	o::init_outputs(oo);
	options o(argc, argv, &ii, &oo);
	bdd::init(o.enabled("bdd-mmap") ? MMAP_WRITE : MMAP_NONE,
		o.get_int("bdd-max-size"), o.get_string("bdd-file"));
	bdd::set_gc_enabled(o.get_bool("gc"));
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
		driver d(o);
		if (d.error) goto quit;
		d.run( (size_t) o.get_int("steps"), (size_t) o.get_int("break") );
		if (d.error) goto quit;
		if (o.enabled("dump") && d.result && !d.out_goals(o::dump()))
			d.dump_fixpoint();
		if (o.enabled("dict")) d.out_dict(o::inf());
		if (o.enabled("csv")) d.save_csv();
#ifdef WITH_THREADS
	}
#endif
quit:
	onexit = true;
	return 0;
}
