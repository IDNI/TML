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
#include "driver.h"
using namespace std;

//void print_memos_len();

int main(int argc, char** argv) {
	setlocale(LC_ALL, "");
	bdd::init();
	driver d(argc, argv, stdin);
	if (!d.result) wcout << "unsat" << endl;
//	print_memos_len();
	return 0;
}
