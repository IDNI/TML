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
#ifdef __unix__
#include <sys/ioctl.h>
#endif
#include "driver.h"
using namespace std;

//void print_memos_len();

bool is_stdin_readable();
bool onexit = false;

int main(int argc, char** argv) {
	setlocale(LC_ALL, "");
	bdd::init();
	driver::init();
	if (is_stdin_readable())
		driver d(file_read_text(stdin), options(argc, argv));
	else {
		strings args;
		if (argc == 1) args = { "-v", "-h" };
		driver d(L"", options(args));
	}
	onexit = true;
//	print_memos_len();
	return 0;
}

bool is_stdin_readable() {
#ifdef __unix__
	long n = 0;
	return ioctl(0, FIONREAD, &n) == 0 && n > 0;
#else // WIN TODO
	return true;
#endif
}
