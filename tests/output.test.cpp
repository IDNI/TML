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
	output o1(L"def");
	if (o1.name() != L"def" || o1.target() != L"@stdout" || o1.is_null())
		return fail(L"create default = @stdout");
	output o2(L"std", L"@stdout");
	if (o2.name() != L"std" || o2.target() != L"@stdout" || o2.is_null())
		return fail(L"create @stdout");
	// STDERR
	output oe(L"err", L"@stderr");
	if (oe.name() != L"err" || oe.target() != L"@stderr" || oe.is_null())
		return fail(L"create @stderr");
	// NULL
	output on(L"null", L"@null");
	if (on.name() != L"null" || on.target() != L"@null" || !on.is_null())
		return fail(L"create @null");
	// BUFFER
	output ob(L"buf", L"@buffer");
	if (ob.name() != L"buf" || ob.target() != L"@buffer" || ob.is_null())
		return fail(L"create @buffer");
	// FILE
	output of(L"file", L"output.test.file");
	if (of.name() != L"file" || of.target() != L"output.test.file" ||
		of.is_null()) return fail(L"create file");
	return ok();
};

test output_null = [] {
	output on(L"null", L"@null"); on << L"discarded";
	if (on.name() != L"null" || on.target() != L"@null" || !on.is_null())
		return fail(L"write @null");
	return ok();
};

test output_std = [] {
	output os(L"std", L"@stdout"); os << L"stdout test";
	output oe(L"err", L"@stderr"); oe << L"stderr test";
	return ok();
};

test output_buffer= [] {
	output ob(L"b", L"@buffer"); ob << L"buffer test";
	if (ob.read() != L"buffer test")
		return fail(L"write @buffer");
	return ok();
};

test output_file = [] {
	{ output of(L"f", L"output.test.file2"); of << L"file test"; }
	if (file_and_mem_cmp("output.test.file2", "file test", 9))
		return fail(L"write file");
	return ok();
};

test output_name = [] {
	outputs oo; oo.use(); oo.target(L"error", L"@buffer");
	oo.create(L"noname", L".noname",L"@name");
	if (oo.read(L"error") !=
		L"output 'noname' targeting @name without setting name\n")
			fail(L"creating @name output without setting --name "
				L"does not raise an err");
	outputs::name(L"named");
	oo.create(L"name1", L".name1", L"@name");
	oo.create(L"name2", L".name2", L"@name");
	outputs::to(L"name1") << L"named1 test" << endl;
	outputs::to(L"name2") << L"named2 test" << endl;
	if (file_and_mem_cmp("named.name1", "named1 test", 11) ||
		file_and_mem_cmp("named.name2", "named2 test", 11))
		return fail(L"write name");
	return ok();
};

test outputs_create = [] {
	outputs oo; oo.use();
	oo.add(output::create(L"stdout", L"@stdout"));
	if (!oo.exists(L"stdout")) fail(L"outputs: created does not exist");
	return ok();
};

test outputs_multiple = [] {
	outputs oo1; oo1.use();
	oo1.add(output::create(L"output_name", L"@buffer"));
	output* o = outputs::get(L"output_name");
	outputs::to(L"output_name") << L"test1";
	*o << L"test2";
	if (o->read() != L"test1test2")
		return fail (L"outputs: oo1 from multiple");

	outputs oo2; oo2.use();
	oo2.add(output::create(L"output_name", L"@buffer"));
	outputs::to(L"output_name") << L"test3";
	o = outputs::get(L"output_name");
	*o << L"test4";
	if (o->read() != L"test3test4")
		return fail (L"outputs: oo2 from multiple");

	oo1.use();
	outputs::to(L"output_name") << L"test5";
	o = outputs::get(L"output_name");
	*o << L"test6";
	if (o->read() != L"test1test2test5test6")
		return fail (L"outputs: oo1 after oo2 from multiple");

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
	wofstream info("output.test.info");
	return run(tests, L"output", &info);
}
