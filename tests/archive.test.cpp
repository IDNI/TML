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
test write_test(const T& value, const char* expected, size_t expected_s) {
	return [value, expected, expected_s] {
		size_t s = archive::size(value);
		archive a(TF1, s, true); a << value;
		if (file_and_mem_cmp(TF1, expected, expected_s))
			return fail("write: failed");
		if (s != expected_s)
			return fail("write: failed (expected size)");
		return ok();
	};
}

template <typename T>
test write_test_ref(const T& value, const char* expected, size_t s) {
	return [&value, expected, s] {
		archive a(TF1, s, true); a << value;
		if (file_and_mem_cmp(TF1, expected, s))
			return fail("write: failed");
		return ok();
	};
}

template <typename T>
test read_test(function<bool(T&)> ok_cond) {
	return [ok_cond] {
		T value;
		archive a(TF1, 0, false); a >> value;
		if (!ok_cond(value)) return fail("read: failed");
		return ok();
	};
};

template <typename T>
test read_test_ref(T& value, function<bool(T&)> ok_cond) {
	return [ok_cond, &value] {
		archive a(TF1, 0, false); a >> value;
		if (!ok_cond(value)) return fail("read: failed");
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
	"\x0c\0\0\0\0\0\0\0Hello World!\0", 21);
test read_string = read_test<string>(
	[](const string& val){ return val == string("Hello World!"); });

dict_t& data_dict_input() {
	static dict_t d;
	if (d.nsyms() == 0) {
		d.get_rel(d.get_lexeme("rel1"));
		d.get_rel(d.get_lexeme("rel2"));
		d.get_sym(d.get_lexeme("symb`ol1"));
		d.get_sym(d.get_lexeme("symb`ol2"));
		d.get_sym(d.get_lexeme("symbol3`"));
		d.get_bltin(d.get_lexeme("blt`in1"));
		d.get_bltin(d.get_lexeme("blt`in2"));
	}
	return d;
}
//test write_dict = write_test_ref<dict_t>(data_dict_input(), 
//	data_dict_expected, data_dict_expected_length);
//test read_dict = read_test<dict_t>([](dict_t& d) {
//	return	d.nrels() == 2 &&
//		d.nsyms() == 3 &&
//		d.nbltins() == 2 &&
//		d.get_rel(1) == "rel2" &&
//		d.get_rel((int_t)0) == "rel1" &&
//		d.get_sym(2) == "symbol3" &&
//		d.get_sym(1) == "symbol2" &&
//		d.get_sym((int_t)0) == "symbol1" &&
//		d.get_bltin(1) == "bltin2" &&
//		d.get_bltin((int_t)0) == "bltin1";
//});

test write_sig = write_test<sig>({ 3000, ints{ -500, 256, 0 } },
	"\xb8\x0b\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00"
	"\x0c\xfe\xff\xff" "\x00\x01\x00\x00" "\x00\x00\x00\x00", 24);
test read_sig = read_test<sig>([] (sig& s) {
	return s.first == 3000 && s.second.size() == 3 &&
		s.second[0] == -500 && s.second[1] == 256 && s.second[2] == 0;
});

test write_bdd_test = [] {
	inputs ii;
	outputs oo; oo.use(); oo.init_defaults();
	bdd::init();
	driver d("a(x). b(y) :- a(x).",	options({ "--no-info", "--no-debug",
		"--no-benchmarks" }, &ii, &oo));
	d.run();
	{ archive a(TF1, archive::bdd_size(), true); a.write_bdd(); }
	if (file_and_mem_cmp(TF1, data_bdd_expected, data_bdd_expected_length))
		return fail("write bdd: failed");
	return ok();
};

test read_bdd_test = [] {
	V->clear();
	{ archive a(TF1, 0, false); a.read_bdd(); }
	bdd_mmap& pV = *V;
	if (pV.size()!=8) return fail("bdd read failed, size does not match");
	for (size_t i = 0; i != 8; ++i)
		if (!(pV[i]==(data_bdd_read_expected[i])))
			return fail("bdd read failed");
	return ok();
};

test write_tables = [] {
	inputs ii;
	outputs oo; oo.use(); oo.init_defaults();
	bdd::init();
	driver d("a(x). b(y) :- a(x).", options({ "--no-info", "--debug",
		"archive.test.debug", "--no-benchmarks" }, &ii, &oo));
	d.run();
	{ archive a(TF1, archive::tables_size(d), true); a.write_tables(d); }
	if (file_and_mem_cmp(TF1, data_tables_expected,
		data_tables_expected_length))
			return fail("write tables: failed");
	return ok();
};

test write_driver = [] {
	inputs ii;
	outputs oo; oo.use(); oo.init_defaults();
	bdd::init();
	driver d("a(x). b(y) :- a(x). c(z) :- b(y).",
		options({ "--no-info", "--debug", "archive.test.debug",
			"--no-benchmarks" }, &ii, &oo));
	d.step();

	COUT << "d.out:" << endl;
	d.out(COUT);

	d.out_dict(COUT << "dict before save: ");

	d.save(TF1);

	if (file_and_mem_cmp(TF1, data_driver_expected,
					data_driver_expected_length))
		//COUT << "write driver: failed\n";
		return fail("write driver: failed");
	return ok();
};

test read_driver = [] {
	inputs ii;
	outputs oo; oo.use(); oo.init_defaults();
	driver d(options(strings{}, &ii, &oo));

	d.load(TF1);

	//d.save(TF2);

	d.out_dict(COUT << "dict after load: ");

	d.run();

	COUT << "d.out:" << endl;
	d.out(COUT);

	return ok();
};

test no_mmap_write_int = [] {
	char data[4], expected[4] = { '\xbd', '\xd0', '\0', '\0' };
	archive a(data, 4); a << 53437;
	if (memcmp(data, expected, 4)) return fail("no mmap write int_t");
	return ok();
};

test no_mmap_read_int = [] {
	char data[4] = { '\xbd', '\xdd', '\0', '\0' };
	archive a(data, 4); int_t r; a >> r;
	if (56765 != r)	return fail("no mmap read int_t");
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
		ostringstream_t ss; ss<<opts;;
		return ws2s(ss.str()) == data_options_read_expected;
	});

	test write_elem_num = write_test<elem>(
		elem(3), "\x02\x03\x00\x00\x00", 5
	);
	test read_elem_num = read_test<elem>([] (elem& e) {
		return e.type == elem::NUM && e.num == 3;
	});
	test write_elem_chr = write_test<elem>(
		elem(U'$'), "\x03\x24\x00\x00\x00", 5
	);
	test read_elem_chr = read_test<elem>([] (elem& e) {
		return e.type == elem::CHR && e.ch == U'$';
	});
	test write_elem_str = write_test<elem>(
		elem(elem::STR, test_dict.get_lexeme("ABC")), "\x08\x03\x00\x00\x00\x00\x00\x00\x00\x41\x42\x43", 12
	);
	test read_elem_str = read_test<elem>([] (elem& e) {
		return e.type == elem::STR && lexeme2str(e.e) == "ABC";
	});

	vector<test> tests = {
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
		write_sig,
		read_sig,
		write_elem_num,
		read_elem_num,
		write_elem_chr,
		read_elem_chr,
		write_options,
		read_options,
		write_bdd_test,
		read_bdd_test,
		write_tables,
//		write_driver,
//		read_driver,
	};

	return run(tests, "archive");
}
