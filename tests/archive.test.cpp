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
#include "../src/archive.h"
#include "simple_test.h"
#include "archive.test.data.h"

#define TF1 "test_file1.bin"
#define TF2 "test_file2.bin"

using namespace std;

dict_t test_dict;

template <typename T>
test write_test(const T& value, const char* expected, size_t s) {
	//wcout << L"creating write test value: " << value << endl;
	return [value, expected, s] {
		//wcout << L"writing: " << value << L" size: " << s << endl;
		archive a(TF1, s, true); a << value;
		if (file_and_mem_cmp(TF1, expected, s))
			return fail(L"write: failed");
		return ok();
	};
}

template <typename T>
test write_test_ref(const T& value, const char* expected, size_t s) {
	//wcout << L"creating write test value: " << value << endl;
	return [&value, expected, s] {
		//wcout << L"writing: " << value << L" size: " << s << endl;
		archive a(TF1, s, true); a << value;
		if (file_and_mem_cmp(TF1, expected, s))
			return fail(L"write: failed");
		return ok();
	};
}

template <typename T>
test read_test(function<bool(T&)> ok_cond) {
	return [ok_cond] {
		T value;
		archive a(TF1, 0, false); a >> value;
		if (!ok_cond(value)) return fail(L"read: failed");
		return ok();
	};
};

template <typename T>
test read_test_ref(T& value, function<bool(T&)> ok_cond) {
	return [ok_cond, &value] {
		archive a(TF1, 0, false); a >> value;
		if (!ok_cond(value)) return fail(L"read: failed");
		return ok();
	};
};

test write_int = write_test<int_t>(53437, "\xbd\xd0\0\0", sizeof(int_t));
test read_int  = read_test<int_t>([](const int_t& v){ return v == 53437; });

test write_unsigned_int = write_test<unsigned int>(
	-53437, "\x43\x2f\xff\xff", sizeof(unsigned int));
test read_unsigned_int  = read_test<unsigned int>(
	[](const unsigned int& val){ return val == -53437; });

test write_size = write_test<size_t>(
	8000000000, "\0\x50\xd6\xDc\x01\0\0\0", sizeof(size_t));
test read_size  = read_test<size_t>(
	[](const size_t& val){ return val == 8000000000; });

test write_char = write_test<char>('0', "\x30", sizeof(char));
test read_char  = read_test<char>([](const char& v){ return v == '0'; });

test write_unsigned_char = write_test<unsigned char>(
	250, "\xfa", sizeof(unsigned char));
test read_unsigned_char  = read_test<unsigned char>([](const unsigned char& v){
	return v == 250; });

test write_string = write_test<string>(string("Hello World!"),
	"\x0c\0\0\0\0\0\0\0Hello World!", 20);
test read_string = read_test<string>(
	[](const string& val){ return val == string("Hello World!"); });

test write_wstring = write_test<wstring>(wstring(L"Hello World!"),
	"\x0c\0\0\0\0\0\0\0Hello World!", 20);
test read_wstring = read_test<wstring>(
	[](const wstring& val){ return val == wstring(L"Hello World!"); });

dict_t& data_dict_input() {
	static dict_t d;
	if (d.nsyms() == 0) {
		d.get_rel(d.get_lexeme(L"rel1"));
		d.get_rel(d.get_lexeme(L"rel2"));
		d.get_sym(d.get_lexeme(L"symbol1"));
		d.get_sym(d.get_lexeme(L"symbol2"));
		d.get_sym(d.get_lexeme(L"symbol3"));
		d.get_bltin(d.get_lexeme(L"bltin1"));
		d.get_bltin(d.get_lexeme(L"bltin2"));
	}
	return d;
}
test write_dict = write_test_ref<dict_t>(data_dict_input(), 
	data_dict_expected, data_dict_expected_length);
test read_dict = read_test<dict_t>([](dict_t& d) {
	return	d.nrels() == 2 &&
		d.nsyms() == 3 &&
		d.nbltins() == 2 &&
		d.get_rel(d.get_lexeme(L"rel2"))     == 1 &&
		d.get_rel(d.get_lexeme(L"rel1"))     == 0 &&
		d.get_sym(d.get_lexeme(L"symbol3"))  == 2 &&
		d.get_sym(d.get_lexeme(L"symbol2"))  == 1 &&
		d.get_sym(d.get_lexeme(L"symbol1"))  == 0 &&
		d.get_bltin(d.get_lexeme(L"bltin2")) == 1 &&
		d.get_bltin(d.get_lexeme(L"bltin1")) == 0;
});

test write_sig = write_test<sig>({ 3000, ints{ -500, 256, 0 } },
	"\xb8\x0b\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00"
	"\x0c\xfe\xff\xff" "\x00\x01\x00\x00" "\x00\x00\x00\x00", 24);
test read_sig = read_test<sig>([] (sig& s) {
	return s.first == 3000 && s.second.size() == 3 &&
		s.second[0] == -500 && s.second[1] == 256 && s.second[2] == 0;
});

test write_bdd_test = [] {
	outputs oo; oo.use(); oo.init_defaults();
	bdd::init();
	driver d(L"a(x). b(y) :- a(x).",
		options({ "--no-info", "--no-debug", "--no-benchmarks" }, &oo));
	d.run();
	{ archive a(TF1, archive::bdd_size(), true); a.write_bdd(); }
	if (file_and_mem_cmp(TF1, data_bdd_expected, data_bdd_expected_length))
		return fail(L"write bdd: failed");
	return ok();
};

test read_bdd_test = [] {
	V->clear();
	{ archive a(TF1, 0, false); a.read_bdd(); }
	bdd_mmap& pV = *V;
	if (pV.size()!=5) return fail(L"bdd read failed, size does not match");
	for (size_t i = 0; i != 5; ++i)
		if (!(pV[i]==(data_bdd_read_expected[i])))
			return fail(L"bdd read failed");
	return ok();
};

test write_tables = [] {
	outputs oo; oo.use(); oo.init_defaults();
	bdd::init();
	driver d(L"a(x). b(y) :- a(x).",
		options({ "--no-info", "--debug", "archive.test.debug",
			"--no-benchmarks" }, &oo));
	d.run();
	{ archive a(TF1, archive::tables_size(d), true); a.write_tables(d); }
	if (file_and_mem_cmp(TF1, data_tables_expected,
		data_tables_expected_length))
			return fail(L"write tables: failed");
	return ok();
};

test write_driver = [] {
	outputs oo; oo.use(); oo.init_defaults();
	bdd::init();
	driver d(L"a(x). b(y) :- a(x). c(z) :- b(y).",
		options({ "--no-info", "--debug", "archive.test.debug",
			"--no-benchmarks" }, &oo));
	d.step();
	size_t s = archive::size(d);
	{ archive a(archive::type::DRIVER, TF1, s, true); a << d; }
	if (file_and_mem_cmp(TF1, data_driver_expected,
					data_driver_expected_length))
		//wcout << L"write driver: failed\n";
		return fail(L"write driver: failed");
	return ok();
};

test read_driver = [] {
	{
		outputs oo; oo.use(); oo.init_defaults();
		driver d(options(strings{}, &oo));
		archive a(archive::type::DRIVER, TF1, 0, false);
		a >> d;

		size_t s = archive::size(d);
		wcout << L"archive::size(d): " << s << endl;

		archive b(archive::type::DRIVER, TF2, s, true);
		b << d;

		d.run();

		wcout << L"d.out:" << endl;
		d.out(wcout);
	}

	return ok();
};

test no_mmap_write_int = [] {
	char data[4], expected[4] = { '\xbd', '\xd0', '\0', '\0' };
	archive a(data, 4); a << 53437;
	if (memcmp(data, expected, 4)) return fail(L"no mmap write int_t");
	return ok();
};

test no_mmap_read_int = [] {
	char data[4] = { '\xbd', '\xdd', '\0', '\0' };
	archive a(data, 4); int_t r; a >> r;
	if (56765 != r)	return fail(L"no mmap read int_t");
	return ok();
};

int main() {
	setlocale(LC_ALL, "");
	outputs oo;
	bdd::init();
	
	test write_options = write_test<options>(
		options(data_options_input),
		data_options_expected,
		data_options_expected_length);

	test read_options = read_test<options>([](options& opts){
		wstringstream ss; ss<<opts;;
		return ss.str() == data_options_read_expected;
	});

	argtypes ats = argtypes(3);
	ats[0] = ats[1] = arg_type{ base_type::INT, 0 };
	ats[2] = arg_type{ base_type::STR, 0 };
	test write_term = write_test<term>(term(24, ints{-5, 3, 0}, ats),
		"\x18\0\0\0\0\0\x03\0\0\0\0\0\0\0\xfb\xff\xff\xff\x03\0", 20);
	term t(0, {}, {});
	test read_term = read_test_ref<term>(t, [](term& t){
		return  t.size() == 3 && t.tab == 24 &&
			t.extype == term::REL && !t.neg && !t.goal &&
			t[0] == -5 && t[1] == 3 && t[2] == 0;
	});

	argtypes types_int = argtypes(1);
	types_int[0] = arg_type{ base_type::INT, 0 };
	//rule r(true, 12, term(12, ints{0}, types_int));
	test write_rule = write_test<rule>(
		rule(true, 12, term(true, (ntable)12, ints{},
			std::vector<ints>{}, types_int)),
			data_rules_expected, data_rules_expected_length);
	rule r(false, -1, term(0, {}, {}));
	test read_rule = read_test_ref<rule>(r, [](rule& r){
		return r.neg && r.tab == 12 && r.len == 0 && r.t.tab == 12 &&
			r.t.neg;
	});

	test write_primitive_type = write_test<primitive_type>(
		primitive_type(base_type::STR, 2, 4),
		"\x03\x02\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00", 13);
	test read_primitive_type = read_test<primitive_type>(
		[](primitive_type& pt) {
			return pt.type == base_type::STR && pt.bitness == 2 &&
				pt.num == 4; });
				
	test write_compound_type = write_test<compound_type>(
		compound_type(vtypes{
			primitive_type(base_type::INT, 4, 32),
			primitive_type(base_type::STR, 2, 3)
		}, true),
		data_compound_expected, data_compound_expected_length);

	test read_compound_type = read_test<compound_type>(
		[](compound_type& ct) {
			return ct == compound_type({
				primitive_type(base_type::INT, 4, 32),
				primitive_type(base_type::STR, 2, 3)
			}, true);
		});

	test write_elem_num = write_test<elem>(
		elem(3), "\x02\x03\x00\x00\x00\x00\x00\x00\x00", 9
	);
	test read_elem_num = read_test<elem>([] (elem& e) {
		return e.type == elem::NUM && e.num == 3;
	});
	test write_elem_chr = write_test<elem>(
		elem(L'₿'), "\x03\xbf\x20\x00\x00\x00\x00\x00\x00", 9
	);
	test read_elem_chr = read_test<elem>([] (elem& e) {
		return e.type == elem::CHR && e.ch == L'₿';
	});
	test write_elem_str = write_test<elem>(
		elem(elem::STR, test_dict.get_lexeme(L"ABC")), "\x08\x03\x00\x00\x00\x00\x00\x00\x00\x41\x42\x43", 12
	);
	test read_elem_str = read_test<elem>([] (elem& e) {
		return e.type == elem::STR && lexeme2str(e.e) == L"ABC";
	});

	vector<test> tests = {
		// lexeme
		// lexeme_range
		// spbdd_handle
		// bitsmeta
		// table
		// raw_term
		// raw_rule
		// raw_prog
		// raw_progs
		// directive
		// production
		// strs_t
		// pair
		// map
		// vector
		// set
		// rcm tuple
		no_mmap_write_int,
		no_mmap_read_int,
		write_int,
		read_int,
		write_unsigned_int,
		read_unsigned_int,
		write_size,
		read_size,
		write_char,
		read_char,
		write_unsigned_char,
		read_unsigned_char,
		write_string,
		read_string,
		write_wstring,
		read_wstring,
		write_dict,
		read_dict,
		write_options,
		read_options,
		write_bdd_test,
		read_bdd_test,
		write_term,
		read_term,
		write_rule,
		read_rule,
		write_sig,
		read_sig,
		write_primitive_type,
		read_primitive_type,
		write_compound_type,
		read_compound_type,
		write_elem_num,
		read_elem_num,
		write_elem_chr,
		read_elem_chr,
		write_elem_str,
		read_elem_str,
		write_tables,
		write_driver,
		read_driver,
	};

	return run(tests, L"archive");
}
