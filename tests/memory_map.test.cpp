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
#include "../src/memory_map.h"
#include "simple_test.h" // f, n, fail(), ok(), run()
#include "../src/bdd.h"

#define TF1 "test_file1.mmap"
#define TF2 "test_file2.mmap"
#define TF3 "test_file3.mmap"
#define S1 3000
#define S2 4096
#define S3 6000

using namespace std;

test create_new_and_open = [] {
	memory_map mm(TF1, S1, MMAP_WRITE);
	if (mm.error) return fail(mm.error_message);
	memory_map mm2(TF1);
	if (mm2.error) return fail(mm2.error_message);
	return ok();
};

// open new memory map for writing and fn does not exist
test open_and_write = [] {
	memory_map mm(TF1, S2, MMAP_WRITE);
	if (mm.error) return fail(mm.error_message);
	char* data = (char*) mm.data();
	if (mm.error) return fail(mm.error_message);
	for (size_t i = 0; i != S2; ++i) data[i] = 255 - (i % 255);
	return ok();
};

// open existing memory map and read
test open_and_read_written = [] {
	memory_map mm(TF1);
	if (mm.error) return fail(mm.error_message);
	char* data = (char*) mm.data();
	if (mm.error) return fail(mm.error_message);
	ostringstream ss;
	for (size_t i = 0; i != S2; ++i) {
		if (data[i] != (char)(255 - (i % 255)))
			return ss << "open_and_read_written pos: " << i
				<< " '" << (int)data[i] << "'", fail(ss.str());
	}
	return ok();
};

// open memory map but file already exists / overwrite
test open_and_overwrite = [] {
	memory_map mm(TF1, S3, MMAP_WRITE);
	if (mm.error) return fail(mm.error_message);
	char* data = (char*) mm.data();
	if (mm.error) return fail(mm.error_message);
	for (size_t i = 0; i != S3; ++i) data[i] = i % 255;
	return ok();
};

// open existing memory map and read it.
test open_and_read_written_again = [] {
	memory_map mm(TF1);
	if (mm.error) return fail(mm.error_message);
	char* data = (char*) mm.data();
	if (mm.error) return fail(mm.error_message);
	ostringstream ss;
	for (size_t i = 0; i != S3; ++i) {
		if (data[i] != (char)(i % 255))
			return ss << "open_and_read_written_again pos: " << i
				<< " '" << (int)data[i] << "'", fail(ss.str());
	}
	return ok();
};

test vector_with_memory_map_allocator_int_t_write = [] {
	bool f = false;
	memory_map_allocator<int_t> a(TF1);
	vector<int_t, memory_map_allocator<int_t> >v(a);
	v.reserve(1000);
	for (int_t i = 0; i != 1000; ++i) v[i] = i-500;
	for (int_t i = 0; i != 1000; ++i)
		if (i-500 != v[i]) { f = true; break; }
	//o::out() << "done" << std::endl;
	if (f) return fail("vector_with_memory_map_allocator_int_t_write");
	return ok();
};

test vector_with_memory_map_allocator_int_t_read = [] {
	//o::out() << "read" << std::endl;
	memory_map_allocator<int_t> a(TF1, MMAP_READ);
	vector<int_t, memory_map_allocator<int_t> > v(a);
	v.reserve(1000);
	bool f = false;
	for (int_t i = 0; i != 1000; ++i)
		if (i-500 != v[i]) { f = true; break; }
	if (f) return fail("vector_with_memory_map_allocator_int_t_read");
	return ok();
};

test mmap_vector_with_nommap_allocator_int_t_write = [] {
	bool f = false;
	memory_map_allocator<int_t> nommap;
	vector<int_t, memory_map_allocator<int_t> > v(nommap);
	v.reserve(1000);
	for (int_t i = 0; i != 1000; ++i) v[i] = i-500;
	for (int_t i = 0; i != 1000; ++i)
		if (i-500 != v[i]) { f = true; break; }
	if (f) return fail("vector_with_memory_map_allocator_int_t_write");
	return ok();
};

test temporary = [] {
	memory_map mm("", S2, MMAP_WRITE);
	if (mm.error) return fail(mm.error_message);
	char* data = (char*) mm.data();
	if (mm.error) return fail(mm.error_message);
	for (size_t i = 0; i != S2; ++i) data[i] = 255 - (i % 255);
	return ok();
};

test bdd_mmap_write = [] {
	std::unique_ptr<bdd_mmap> pM;
	pM = std::make_unique<bdd_mmap>();
	pM->emplace_back(0,0,0);
	pM->emplace_back(1,1,1);
	pM = 0;
	pM = std::make_unique<bdd_mmap>(
		memory_map_allocator<bdd>(TF1, MMAP_WRITE));
	pM->reserve(2);
	pM->emplace_back(0,0,0);
	pM->emplace_back(1,1,1);
	return ok();
};

int main() {
	setlocale(LC_ALL, "");
	outputs oo;
	oo.target("debug",  "@stdout");
	oo.target("output", "@stdout");
	vector<test> tests = {
		create_new_and_open,
		open_and_write,
		open_and_read_written,
		open_and_overwrite,
		open_and_read_written_again,
		vector_with_memory_map_allocator_int_t_write,
		vector_with_memory_map_allocator_int_t_read,
		mmap_vector_with_nommap_allocator_int_t_write,
		temporary,
		bdd_mmap_write,
	};
	return run(tests, "memory_map");
}
