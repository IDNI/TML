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
#include "../src/output.h"
#include "simple_test.h"

using namespace std;

test output_create = [] {
	// STDOUT
	output o1("def");
	if (o1.name() != "def" || o1.target() != "@stdout" || o1.is_null())
		return fail("create default = @stdout");
	output o2("std", "@stdout");
	if (o2.name() != "std" || o2.target() != "@stdout" || o2.is_null())
		return fail("create @stdout");
	// STDERR
	output oe("err", "@stderr");
	if (oe.name() != "err" || oe.target() != "@stderr" || oe.is_null())
		return fail("create @stderr");
	// NULL
	output on("null", "@null");
	if (on.name() != "null" || on.target() != "@null" || !on.is_null())
		return fail("create @null");
	// BUFFER
	output ob("buf", "@buffer");
	if (ob.name() != "buf" || ob.target() != "@buffer" || ob.is_null())
		return fail("create @buffer");
	// FILE
	output of("file", "output.test.file");
	if (of.name() != "file" || of.target() != "output.test.file" ||
		of.is_null()) return fail("create file");
	return ok();
};

test output_null = [] {
	output on("null", "@null"); on << "discarded";
	if (on.name() != "null" || on.target() != "@null" || !on.is_null())
		return fail("write @null");
	return ok();
};

test output_std = [] {
	output os("std", "@stdout"); os << "stdout test";
	output oe("err", "@stderr"); oe << "stderr test";
	return ok();
};

test output_buffer= [] {
	output ob("b", "@buffer"); ob << "buffer test";
	if (ws2s(ob.read()) != "buffer test")
		return fail("write @buffer");
	return ok();
};

test output_file = [] {
	{ output of("f", "output.test.file2"); of << "file test"; }
	if (file_and_mem_cmp("output.test.file2", "file test", 9))
		return fail("write file");
	return ok();
};

test output_name = [] {
	outputs oo; oo.use(); oo.target("error", "@buffer");
	oo.create("noname", ".noname","@name");
	if (ws2s(oo.read("error")) !=
		"output 'noname' targeting @name without setting name\n")
			fail("creating @name output without setting --name "
				"does not raise an err");
	outputs::name("named");
	oo.create("name1", ".name1", "@name");
	oo.create("name2", ".name2", "@name");
	outputs::to("name1") << "named1 test" << endl;
	outputs::to("name2") << "named2 test" << endl;
	if (file_and_mem_cmp("named.name1", "named1 test", 11) ||
		file_and_mem_cmp("named.name2", "named2 test", 11))
		return fail("write name");
	return ok();
};

test outputs_create = [] {
	outputs oo; oo.use();
	oo.add(output::create("stdout", "@stdout"));
	if (!oo.exists("stdout")) fail("outputs: created does not exist");
	return ok();
};

test outputs_multiple = [] {
	outputs oo1; oo1.use();
	oo1.add(output::create("output_name", "@buffer"));
	output* o = outputs::get("output_name");
	outputs::to("output_name") << "test1";
	*o << "test2";
	if (ws2s(o->read()) != "test1test2")
		return fail ("outputs: oo1 from multiple");

	outputs oo2; oo2.use();
	oo2.add(output::create("output_name", "@buffer"));
	outputs::to("output_name") << "test3";
	o = outputs::get("output_name");
	*o << "test4";
	if (ws2s(o->read()) != "test3test4")
		return fail ("outputs: oo2 from multiple");

	oo1.use();
	outputs::to("output_name") << "test5";
	o = outputs::get("output_name");
	*o << "test6";
	if (ws2s(o->read()) != "test1test2test5test6")
		return fail ("outputs: oo1 after oo2 from multiple");

	return ok();
};

int main() {
	setlocale(LC_ALL, "");
	vector<test> tests = {
		output_create,
		output_null,
		output_std,
		output_buffer,
		output_file,
		output_name,
		outputs_create,
		outputs_multiple
	};
	ofstream_t info("output.test.info");
	return run(tests, "output", &info);
}
