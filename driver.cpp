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

#ifdef DEBUG
driver* drv;
#endif

wostream& operator<<(wostream& os, const pair<cws, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

wostream& driver::printbdd(wostream& os, size_t t) const {
	return printbdd(os, progs.back()->getbdd(t));
}
wostream& driver::printdb(wostream& os, size_t prog) const {
	return printbdd(os, progs[prog]->db);
}

pair<cws, size_t> driver::dict_get(int_t t) const {
	static wchar_t str_nums[20], str_chr[] = L"'a'";
	if (t >= nums) return { syms[t - nums], lens[t - nums] };
	if (t < 256) { str_chr[1] = t; return { str_chr, (size_t)3 }; }
	wcscpy(str_nums, to_wstring(t-256).c_str());
	return { str_nums, wcslen(str_nums) };
}

int_t driver::dict_get(cws s, size_t len) {
	if (!s) return pad;
	if (iswdigit(*s)) er("symbol name cannot begin with a digit");
	if (*s == L'?') {
		auto it = vars_dict.find({s, len});
		if (it != vars_dict.end()) return it->second;
		int_t r = -vars_dict.size() - 1;
		return vars_dict[{s, len}] = r;
	}
	auto it = syms_dict.find({s, len});
	if (it != syms_dict.end()) return it->second;
	return	syms.push_back(s), lens.push_back(len), syms_dict[{s,len}] =
		syms.size() - 1 + nums;
}

int_t driver::dict_get(const lexeme& l) { return dict_get(l[0], l[1]-l[0]); }

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

term driver::get_term(const raw_term& r) {
	term t;
	t.push_back(r.neg ? -1 : 1);
	for (const elem& e : r.e)
		if (e.type == elem::NUM) t.push_back(e.num);
		else if (e.type == elem::CHR) t.push_back(*e.e[0]);
		else t.push_back(dict_get(e.e));
	return t;
}

matrix driver::get_rule(const raw_rule& r) {
	matrix m;
	m.push_back(get_term(r.h));
	for (auto x : r.b) m.push_back(get_term(x));
	return m;
}

void driver::term_pad(term& t, size_t ar) {
	size_t l;
	if ((l=t.size())<ar+1) t.resize(ar+1), fill(t.begin()+l, t.end(), pad);
}

void driver::rule_pad(matrix& t, size_t ar) { for (term& x:t) term_pad(x, ar); }

matrix driver::rule_pad(const matrix& t, size_t ar) {
	matrix r;
	rule_pad(r = t, ar);
	return r;
}

driver::driver(FILE *f, bool proof) {
	DBG(drv = this;)
	const raw_progs rp(f);
	for (size_t n = 0; n != rp.p.size(); ++n) {
		strs.emplace_back();
		for (size_t k = 0; k != rp.p[n].d.size(); ++k) {
			const directive& d = rp.p[n].d[k];
			wstring str;
			if (d.fname) {
				wstring wfname(d.arg[0]+1, d.arg[1]-d.arg[0]-1);
				string fname(wfname.begin(), wfname.end());
				nums=max(nums, 256+(int_t)fsize(fname.c_str()));
			} else nums = max(nums, 256+d.arg[1]-d.arg[0]);
		}
	}
	static wstr spad;
	pad = dict_get(spad, 0);
	size_t ar = 0;
	for (size_t n = 0; n != rp.p.size(); ++n) {
		for (size_t k = 0; k != rp.p[n].d.size(); ++k) {
			ar = max(ar, (size_t)4);
			const directive& d = rp.p[n].d[k];
			wstring str(d.arg[0] + 1, d.arg[1] - d.arg[0] - 1);
			strs[n].emplace(dict_get(d.rel), d.fname ?
				file_read_text(str) : str);
		}
		set<matrix> s;
		for (auto x : rp.p[n].r) {
			ar = max(ar, x.h.e.size());
			for (auto e:x.h.e) if (e.type==elem::SYM) dict_get(e.e);
			for (auto y : x.b) {
				ar = max(ar, y.e.size());
				for (auto e : y.e)
					if (e.type==elem::SYM) dict_get(e.e);
			}
		}
	}
	for (size_t n = 0; n != rp.p.size(); ++n) {
		set<matrix> m;
		proofs.emplace_back();
		for (auto x : rp.p[n].r) m.insert(get_rule(x));
		prog_add(move(m), ar, strs[n], proof ? &proofs.back() : 0);
	}
}

void driver::prog_add(set<matrix> m, size_t ar, const map<int_t, wstring>& s,
	set<matrix>* proof) {
	progs.emplace_back(new lp(dict_bits(), ar, nsyms()));
	for (auto x : s)
		for (int_t n = 0; n != (int_t)x.second.size(); ++n)
			progs.back()->rule_add(rule_pad({{ 1, x.first,
				n + 256, x.second[n], n + 257 }}, ar), proof);
	while (!m.empty()) {
		matrix x = move(*m.begin());
		m.erase(m.begin());
		progs.back()->rule_add(rule_pad(move(x), ar), proof);
	}
}

bool driver::pfp(lp *p, set<matrix>* proof) {
	set<size_t> pr;
	size_t d, add, del, t;
	for (set<int_t> s;;) {
		add=del=F, s.emplace(d = p->db), p->fwd(add, del, proof?&pr:0);
		if ((t = bdd_and_not(add, del)) == F && add != F)
			p->db = F; // detect contradiction
		else p->db = bdd_or(bdd_and_not(p->db, del), t);
		if (d == p->db) break;
		if (s.find(p->db) != s.end()) return false;
	}
	if (!proof) return true;
	strs.emplace_back();
	size_t ar = 0;
	for (const matrix& x : *proof)
		for (const term& y : x) ar = max(ar, y.size() - 1);
	//for (const matrix& x : *proof) wcout << x << endl;
	prog_add(move(*proof), ar, strs.back(), 0);
	lp *q = progs.back();
	q->db = add = del = F;
	for (size_t x : pr) q->db = bdd_or(q->db, x);
	q->fwd(add, del, 0);
	printbdd(wcout, add);
	delete q;
	return true;
}

bool driver::pfp(bool pr) {
	size_t sz = progs.size();
	pfp(progs[0], pr ? &proofs[0] : 0);
	for (size_t n = 1; n != sz; ++n) {
		progs[n]->db = progs[n-1]->db;
		if (!pfp(progs[n], pr ? &proofs[n] : 0)) return false;
	}
	return printdb(wcout, sz - 1), true;
}

int main(int argc, char** argv) {
	setlocale(LC_ALL, ""), tml_init();
	//parser_test();
	bool proof = argc == 2 && !strcmp(argv[1], "-p");
	driver d(stdin, proof);
	if (!d.pfp(proof)) wcout << "unsat" << endl;
	return 0;
}
