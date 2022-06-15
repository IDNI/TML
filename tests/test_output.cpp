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
#include "unittest.hpp"
#include "../src/output.h"

TEST_SUITE("output class") {
TEST_CASE("create") {
	output o1("def");
	output o2("std", "@stdout");
	output oe("err", "@stderr");
	output on("null", "@null");
	output ob("buf", "@buffer");
	output of("file", "output.test.file");
	EXPECT_TRUE(o1.name() == "def" && o1.target() == "@stdout"
		&& !o1.is_null());
	EXPECT_TRUE(o2.name() == "std" && o2.target() == "@stdout"
		&& !o2.is_null());
	EXPECT_TRUE(oe.name() == "err" && oe.target() == "@stderr"
		&& !oe.is_null());
	EXPECT_TRUE(on.name() == "null" && on.target() == "@null"
		&& on.is_null());
	EXPECT_TRUE(ob.name() == "buf" && ob.target() == "@buffer"
		&& !ob.is_null());
	EXPECT_TRUE(of.name() == "file" && of.target() == "output.test.file"
		&& !of.is_null());
}
TEST_CASE("null") {
	output on("null", "@null"); on << "discarded";
	EXPECT_TRUE(on.name() == "null" && on.target() == "@null"
		&& on.is_null());
}
TEST_CASE("std") {
	output os("std", "@stdout"); os << "stdout test\n";
	output oe("err", "@stderr"); oe << "stderr test\n";
	EXPECT_TRUE(os.name() == "std" && os.target() == "@stdout"
		&& !os.is_null());
	EXPECT_TRUE(oe.name() == "err" && oe.target() == "@stderr"
		&& !oe.is_null());
}
TEST_CASE("buffer") {
	output ob("b", "@buffer"); ob << "buffer test";
	CHECK(ws2s(ob.read()) == "buffer test");
}
TEST_CASE("file") {
	{
		output of("f", "output.test.file2"); of << "file test";
		EXPECT_TRUE(of.name() == "f"
			&& of.target() == "output.test.file2" && !of.is_null());
	}
}
}
TEST_SUITE("outputs class") {
TEST_CASE("create") {
	outputs oo; oo.use();
	oo.add(output::create("stdout", "@stdout"));
	EXPECT_TRUE(oo.exists("stdout"));
}
TEST_CASE("multiple") {
	outputs oo1; oo1.use();
	oo1.add(output::create("output_name", "@buffer"));
	output* o = outputs::get("output_name");
	outputs::to("output_name") << "test1";
	*o << "test2";
	CHECK(ws2s(o->read()) == "test1test2");

	outputs oo2; oo2.use();
	oo2.add(output::create("output_name", "@buffer"));
	outputs::to("output_name") << "test3";
	o = outputs::get("output_name");
	*o << "test4";
	CHECK(ws2s(o->read()) == "test3test4");

	oo1.use();
	outputs::to("output_name") << "test5";
	o = outputs::get("output_name");
	*o << "test6";
	CHECK(ws2s(o->read()) == "test1test2test5test6");
}
TEST_CASE("name") {
	outputs oo; 
	o::init_outputs(oo);
	oo.use(); oo.target("error", "@buffer");
	oo.create("noname", ".noname","@name");
	CHECK(ws2s(oo.read("error")) ==
		"output 'noname' targeting @name without setting name\n");
	outputs::name("named");
	oo.create("name1", ".name1", "@name");
	oo.create("name2", ".name2", "@name");
	outputs::to("name1") << "named1 test\n";
	outputs::to("name2") << "named2 test\n";
}
}
