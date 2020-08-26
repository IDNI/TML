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
#include "../src/input.h"
#include "simple_test.h"

using namespace std;

test string_input = [] {
	ccs s = "string";
	input i(s);
	if (i.begin() != i.data())
		return fail("input beg != data");
	return ok();
};

test file_input = [] {
	input i(string("input.test.file"));
	if (i.begin() != i.data())
		return fail("input beg != data");
	return ok();
};

test multiple_inputs = [] {

	string
		prog1 = "a. b :- a.",
		prog2 = "c. d :- a, b, c.",
		prog3 = "a.\nb.\nc :- a, b.\n";

	inputs ii;
	if (ii.size() != 0) return fail("inputs size != 0");
	if (ii.current() != 0) return fail("empty inputs current != 0");

	ii.add_string(prog1);
	if (ii.size() != 1) return fail("inputs size != 1");
	if (ii.current() != 0) return fail("inputs(of size 1) current != 0");

	ii.add_string(prog2);
	if (ii.size() != 2) return fail("inputs size != 2");
	if (ii.current() != 0) return fail("inputs(of size 2) current != 0");

	ii.add_file("input.test.file");
	if (ii.size() != 3) return fail("inputs size != 3");
	if (ii.current() != 0) return fail("inputs(of size 3) current != 0");

	input* i = ii.next();
	if (ii.current() != i) return fail("input1 current error");
	if (i == 0) return fail("input1 next == 0");
	if ((string(i->data())  != prog1)
 	 || (string(i->begin()) != prog1))
		return fail("wrong input1 data");

	i = ii.next();
	if (ii.current() != i) return fail("input2 current error");
	if (i == 0) return fail("input2 next == 0");
	if ((string(i->data())  != prog2)
	 || (string(i->begin()) != prog2))
		return fail("wrong input2 data");

	i = ii.next();
	if (ii.current() != i) return fail("input3 current error");
	if (i == 0) return fail("input3 == 0");
	//COUT << "prog3: '" << prog3 << "'\n i->begin(): '"
	//	<< i->begin() << "'\n";
	if ((string(i->data())  != prog3)
	 || (string(i->begin()) != prog3))
		return fail("wrong input3 data");

	return ok();
};

int main() {
	setlocale(LC_ALL, "");
	vector<test> tests = {
		string_input,
		file_input,
		multiple_inputs,
	};
	return run(tests, "input");
}
