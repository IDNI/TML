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
#include <map>
#include <set>
#include <string>
#include <cstring>
#include <sstream>
#include <forward_list>
#include "driver.h"
using namespace std;

#define oparen_expected "'(' expected\n"
#define comma_expected "',' or ')' expected\n"
#define dot_after_q "expected '.' after query.\n"
#define if_expected "'if' or '.' expected\n"
#define sep_expected "Term or ':-' or '.' expected\n"
#define unmatched_quotes "Unmatched \"\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"
#define err_quotes "expected \"."
#define err_dots "two consecutive dots, or dot in beginning of document."
#define msb(x) ((sizeof(unsigned long long)<<3) - \
	__builtin_clzll((unsigned long long)(x)))

struct dictcmp {
	bool operator()(const pair<wstr, size_t>& x,
			const pair<wstr, size_t>& y) const {
		return	x.second != y.second ? x.second < y.second :
			wcsncmp(x.first, y.first, x.second) < 0;
	}
};

map<pair<wstr, size_t>, int_t, dictcmp> syms_dict, vars_dict;
vector<wstr> syms;
vector<size_t> lens;
wstring file_read_text(FILE *f);

void dict_init() { syms.push_back(0), lens.push_back(0), syms_dict[{0, 0}]=pad;}
pair<wstr, size_t> dict_get(int_t t) { return { syms[t],lens[t] }; }
size_t nsyms() { return syms.size(); }

wostream& operator<<(wostream& os, const pair<wstr, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

#ifdef DEBUG
driver* drv;
driver::driver() { drv = this; }
#endif

wostream& driver::printbdd(wostream& os, const lp& p, size_t t) const {
	return printbdd(os, p.getbdd(t));
}
wostream& driver::printbdd(wostream& os, size_t t) const {
	return printbdd(os, progs.back()->getbdd(t));
}
wostream& driver::printdb(wostream& os, lp *q) const {
	return printbdd(os, q->getdb());
}

int_t dict_get(wstr s, size_t len) {
	if (*s == L'?') {
		auto it = vars_dict.find({s, len});
		if (it != vars_dict.end()) return it->second;
		int_t r = -vars_dict.size() - 1;
		return vars_dict[{s, len}] = r;
	}
	auto it = syms_dict.find({s, len});
	if (it != syms_dict.end()) return it->second;
	return	syms.push_back(s), lens.push_back(len), syms_dict[{s,len}] =
		syms.size() - 1;
}

size_t dict_bits() { return msb(nsyms()-1); }

wostream& driver::printbdd(wostream& os, const matrix& t) const {
	set<wstring> s;
	for (auto v : t) {
		wstringstream ss;
		for (auto k : v)
			if (k == pad) ss << L"* ";
			else if((size_t)k<(size_t)nsyms())ss<<dict_get(k)<<L' ';
			else ss << L'[' << k << L"] ";
		s.emplace(ss.str());
	}
	for (auto& x : s) os << x << endl;
	return os;
}

int_t driver::str_read(wstr *s) {
	wstr t;
	while (**s && iswspace(**s)) ++*s;
	if (!**s) throw runtime_error("identifier expected");
	if (*(t = *s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
	if (t == *s) throw runtime_error("identifier expected");
	int_t r = dict_get(*s, t - *s);
	while (*t && iswspace(*t)) ++t;
	return *s = t, r;
}

term driver::term_read(wstr *s) {
	term r;
	while (iswspace(**s)) ++*s;
	if (!**s) return r;
	bool b = **s == L'~';
	if (b) ++*s, r.push_back(-1); else r.push_back(1);
	do {
		while (iswspace(**s)) ++*s;
		if (**s == L',') return ++*s, r;
		if (**s == L'.' || **s == L':') return r;
		r.push_back(str_read(s));
	} while (**s);
	er("term_read(): unexpected parsing error");
}

matrix driver::rule_read(wstr *s) {
	term t;
	matrix r;
	if ((t = term_read(s)).empty()) return r;
	r.push_back(t);
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return ++*s, r;
	if (*((*s)++) != L':' || *((*s)++) != L'-') er(sep_expected);
loop:	if ((t = term_read(s)).empty()) er("term expected.");
	r.push_back(t);
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return ++*s, r;
	if (**s == L':') er("unexpected ':'.");
	goto loop;
}
/*
void directive_read(wstr s) {
	wstr ss = s;
	if(wcsncmp(++s, L"load", 4) && iswspace(*(s += 4))) {
		while (iswspace(*s)) ++s;
		if (*s == L'"') {
			wstring fname, txt;
			while (*++s != L'"')
				if (!*s) er(err_quotes);
				else fname += *s;
			FILE* f = fopen((const char*)fname.c_str(),"r");
			txt = file_read_text(f);
			fclose(f);
			const char* ctxt = (const char*)txt.c_str();
		}
	}
	while (ss != s) *(ss++) = L' ';
}
*/
lp* driver::prog_read(wstr *s, bool proof) {
	/*bool dot = true;
	for (wstr ss = s; *ss; ++ss) {
		if (iswspace(*ss)) continue;
		if (*ss == L'.') {
			if (dot) er(err_dots);
			dot = true;
		}
		if (dot) {
			if (*ss == L'@') directive_read(ss);
			dot = false;
		}
	}*/
	set<matrix> rules;
	for (matrix t; !(t = rule_read(s)).empty(); rules.emplace(t)) {
		while (iswspace(**s)) ++*s;
		if (**s == L'}') {
			if (!mult) er("unexpected '}'");
			rules.emplace(t);
			break;
		} 
		if (**s == L'{') er("unexpected '{'");
	}
	return prog_create(move(rules), proof);
}

lp* driver::prog_create(set<matrix> rules, bool proof) {
	size_t ar = 0, l;
	for (const matrix& t : rules)
		for (const term& x : t)
			ar = max(ar, x.size() - 1);
	lp *p = new lp(dict_bits(), ar, nsyms());
	while (!rules.empty()) {
		matrix t = *rules.begin();
		rules.erase(rules.begin());
		for (term& x : t)
			if ((l = x.size()) < ar+1) x.resize(ar+1),
				fill(x.begin() + l, x.end(), pad);
		p->rule_add(t, proof ? &proofs.back() : 0);
	}
	return p;
}

void driver::progs_read(wstr s, bool proof) {
	while (iswspace(*s)) ++s;
	if (!(mult = *s == L'{')) {
		if (proof) proofs.emplace_back();
		progs.push_back(prog_read(&s, proof));
		return;
	}
	while (*s) {
		while (iswspace(*s)) ++s;
		if (*s == L'{') {
			if (proof) proofs.emplace_back();
			progs.push_back(prog_read(&++s, proof));
		}
		while (iswspace(*s)) ++s;
		if (*s != L'}') er("expected '}'");
		else ++s;
		while (iswspace(*s)) ++s;
	}
}

wstring file_read_text(FILE *f) {
	wstringstream ss;
	wchar_t buf[32], n, l, skip = 0;
	wint_t c;
	*buf = 0;
next:	for (n = l = 0; n != 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = 0; break; }
		else if (c == L'#') skip = 1;
		else if (c == L'\r' || c == L'\n') skip = 0, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0, ss << buf;
		goto next;
	} else if (skip) goto next;
	return ss.str();
}

bool driver::pfp(lp *p, set<matrix>* proof) {
	set<size_t> pr;
	size_t d, add, del, t;
	for (set<int_t> s;;) {
		add = del = F;
		s.emplace(d = p->db), p->fwd(add, del, proof ? &pr : 0);
		if ((t = bdd_and_not(add, del)) == F && add != F)
			p->db = F; // detect contradiction
		else p->db = bdd_or(bdd_and_not(p->db, del), t);
		if (s.find(p->db) != s.end()) {
			if (d != p->db) return false;
			break;
		}
	}
	if (!proof) return true;
	lp *q = prog_create(move(*proof), false);
	q->db = add = del = F;
	for (size_t x : pr) q->db = bdd_or(q->db, x);
	q->fwd(add, del, 0);
	printbdd(wcout, *q, add);
	delete q;
	return true;
}

bool driver::pfp(bool pr) {
	pfp(progs[0], pr ? &proofs[0] : 0);
	for (size_t n = 1; n != progs.size(); ++n) {
		progs[n]->db = progs[n-1]->db;
		if (!pfp(progs[n], pr ? &proofs[n] : 0)) return false;
	}
	return printdb(wcout, progs.back()), true;
}

int main(int argc, char** argv) {
	setlocale(LC_ALL, ""), tml_init(), dict_init();
	bool proof = argc == 2 && !strcmp(argv[1], "-p");
	driver d;
	wstring s = file_read_text(stdin); // got to stay in memory
	wstr str = wcsdup(s.c_str());
	s.clear();
	d.progs_read(str, proof);
	if (!d.pfp(proof)) wcout << "unsat" << endl;
	free(str);
	return 0;
}
