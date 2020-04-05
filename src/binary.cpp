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
#include "driver.h"

using namespace std;

//#define mksym(x) (int_t(x)<<2)

// binary format of a source, dict and resulting bdd database
//------------------------------------------------------------------------------
//
// header  (0xbdd0)
// version (0x0000)
// dict:
//     int_t nrels
//     nrels * cstr rel
//     int_t nsyms
//     nsyms * cstr sym
// int_t bits
// int_t nums
// int_t nnodes (V.size())
// nnodes * (int_t v, int h, int l)
// cstr source
//
// usage:
//     ostream << driver
//     istream >> driver

ostream& write_int(ostream& os, int_t v);
ostream& write_string(ostream& os, const lexeme& l);
ostream& write_string(ostream& os, const wstring& s);
ostream& write_string(ostream& os, const string& s);
ostream& write_bdd(ostream& os);
ostream& operator<<(ostream& os, const lexeme& l);
ostream& operator<<(ostream& os, const dict_t& d);
ostream& operator<<(ostream& os, const tables& tbl);
ostream& operator<<(ostream& os, const driver& d);

int_t read_int(istream& is);
wstring read_string(istream& is);
istream& read_bdd(istream& is);
istream& operator>>(istream& is, dict_t& d);
istream& operator>>(istream& is, tables& tbl);
istream& operator>>(istream& is, driver& d);


// serializing
//------------------------------------------------------------------------------

ostream& write_string(ostream& os, const lexeme& l) {
	return write_string(os, wstring(l[0], l[1]-l[0]));
}

ostream& write_string(ostream& os, const wstring& ws) {
	return write_string(os, ws2s(ws));
}

ostream& write_string(ostream& os, const string& s) {
	os.write(reinterpret_cast<const char *>(s.c_str()), s.size());
	os.write("\0", sizeof(char));
	return os;
}

ostream& write_int(ostream& os, int_t v) {
	os.write(reinterpret_cast<const char *>(&v), sizeof(int_t));
	return os;
}

ostream& operator<<(ostream& os, const lexeme& l) {
	return write_string(os, wstring(l[0], l[1]-l[0]));
}

ostream& operator<<(ostream& os, const dict_t& d) {
	write_int(os, d.nrels());
	for (size_t i = 0; i != d.nrels(); ++i)
		write_string(os, d.get_rel(i));
	write_int(os, d.nsyms());
	// D: this no longer works (<< >>2 for sym, num, chr), use just 'i'
	for (size_t i = 0; i != d.nsyms(); ++i)
		write_string(os, d.get_sym(mksym(i))); // i<<2
	return os;
}

ostream& operator<<(ostream& os, const tables& tbl) {
	os << tbl.dict;
	// D: this needs to be reimplemented, bits no more (as such)
	//write_int(os, tbl.bits);
	//write_int(os, tbl.nums);
	return os;
}

ostream& write_bdd(ostream& os) {
	write_int(os, V.size()-2);
	for (auto b = V.begin()+2; b < V.end(); ++b) {
		//DBG(o::out()<<L"v: "<<b->v<<L" h: "<<b->h<<L" l: "<<b->l<<endl;)
		write_int(os, b->v);
		write_int(os, b->h);
		write_int(os, b->l);
	}
	return os;
}

ostream& operator<<(ostream& os, const driver& d) {
	write_int(os, 53437); // 0xbdd00000
	if (!d.tbl) for (size_t i = 0; i != 4; ++i) write_int(os, 0);
	else os << *d.tbl;
	write_bdd(os);
	return os << input::source;
}


// unserializing
//------------------------------------------------------------------------------

int_t read_int(istream& is) {
	int_t v;
	is.read(reinterpret_cast<char *>(&v), sizeof(int_t));
	return v;
}

wstring read_string(istream& is) {
	stringstream ss;
	char p;
	while (is.read(&p, sizeof(char)), p) ss << p;
	return s2ws(ss.str());
}

istream& read_bdd(istream& is) {
	int_t nnodes = read_int(is);
	bdd::gc();
	V.clear();
	bdd::init();
	DBG(o::out() << L"nnodes: " << nnodes << endl;)
	for (int_t i = 0; i != nnodes; ++i) {
		int_t v = read_int(is), h = read_int(is), l = read_int(is);
		DBG(o::out()<<L"v: "<<v<<L" h: "<<h<<L" l: "<<l<<endl;)
		V.emplace_back(v, h, l);
	}
	return is;
}

istream& operator>>(istream& is, dict_t& d) {
	int_t nrels = read_int(is);
	DBG(o::out() << L"nrels: " << nrels << endl;)
	for (int_t i = 0; i != nrels; ++i) {
		wstring t = read_string(is);
		DBG(o::out() << L"\t`" << t << L'`' << endl;)
		d.get_rel(t);
	}
	int_t nsyms = read_int(is);
	DBG(o::out() << L"nsyms: " << nsyms << endl;)
	for (int_t i = 0; i != nsyms; ++i) {
		wstring t = read_string(is);
		DBG(o::out() << L"\t`" << t << L'`' << endl;);
		// D: TODO: this might no longer work, it's just for syms, no shifting.
		d.get_sym(d.get_lexeme(t));
	}
	return is;
}

istream& operator>>(istream& is, tables& tbl) {
	is >> tbl.dict;
	// D: this needs to be reimplemented, bits no more (as such)
	//tbl.bits = read_int(is);
	//DBG(o::out() << L"bits: " << tbl.bits << endl;)
	//tbl.nums = read_int(is);
	//DBG(o::out() << L"nums: " << tbl.nums << endl;)
	return is;
}

istream& operator>>(istream& is, driver& d) {
	read_int(is); // should be 53437
	is >> *d.tbl;
	read_bdd(is);
	wstring source = read_string(is);
	DBG(o::out()<<L"source: `"<<source<<L"`"<<endl;)
	return is;
}
