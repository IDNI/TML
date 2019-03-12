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

wostream& driver::printbdd(wostream& os, size_t prog, size_t t) const {
	return printbdd(os, progs[prog]->getbdd(t), prog);
}
wostream& driver::printbdd(wostream& os, size_t t) const {
	return printbdd(os, progs.back()->getbdd(t), progs.size()-1);
}
wostream& driver::printdb(wostream& os, size_t prog) const {
	return printbdd(os, prog, progs[prog]->db);
}

pair<cws, size_t> driver::dict_get(int_t t) const {
	static wchar_t str_nums[20];
	if (t >= nums) return { syms[t], lens[t] };
	wcscpy(str_nums, to_wstring(t).c_str());
	return { str_nums, wcslen(str_nums) };
}

int_t driver::dict_get(cws s, size_t len) {
	if (iswdigit(*s)) er("symbol name cannot begin with a digit");
	if (*s == L'?') {
		auto it = vars_dict.find({s, len});
		if (it != vars_dict.end()) return it->second;
		int_t r = -vars_dict.size() - 1;
		return vars_dict[{s, len}] = r;
	}
	auto it = syms_dict.find({s, len});
	if (it != syms_dict.end()) return it->second;
	assert(!nums);
	return	syms.push_back(s), lens.push_back(len), syms_dict[{s,len}] =
		syms.size() - 1 + nums;
}

int_t driver::dict_get(const lexeme& l) { return dict_get(l[0], l[1]-l[0]); }

wostream& driver::printbdd(wostream& os, const matrix& t, size_t prog) const {
	set<wstring> s;
	for (auto v : t) {
		wstringstream ss;
		auto it = strs[prog].find(v[0]);
		if (it == strs[prog].end()) {
			for (auto k : v)
				if (k == pad) ss << L"* ";
				else if ((size_t)k<(size_t)nsyms())
					ss<<dict_get(k)<<L' ';
				else ss << L'[' << k << L"] ";
		} else
			ss << dict_get(v[0]) << ' ' << v[1] - syms.size()
			<< " '" << (wchar_t)(v[2] - syms.size())
			<< "' " << v[3] - syms.size();
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
	return t.push_back(pad), t;
}

matrix driver::get_rule(const raw_rule& r) {
	matrix m;
	m.push_back(get_term(r.h));
	for (auto x : r.b) m.push_back(get_term(x));
	return m;
}

driver::driver(FILE *f, bool proof) {
	syms.push_back(0), lens.push_back(0), syms_dict[{0, 0}] = pad;
	DBG(drv = this;)
	const raw_progs rp(f);
	for (size_t n = 0; n != rp.p.size(); ++n) {
		strs.emplace_back();
		for (size_t k = 0; k != rp.p[n].d.size(); ++k) {
			const directive& d = rp.p[n].d[k];
			wstring str;
			nums = max(nums, (int_t)256);
			if (d.fname) {
				wstring fname(d.arg[0]+1, d.arg[1]-d.arg[0]-1);
				nums = max(nums,
				(int_t)fsize((const char*)fname.c_str()));
			} else nums = max(nums, d.arg[1]-d.arg[0]);
		}
	}
	for (size_t n = 0; n != rp.p.size(); ++n) {
		for (size_t k = 0; k != rp.p[n].d.size(); ++k) {
			const directive& d = rp.p[n].d[k];
			wstring str(d.arg[0]+1, d.arg[1]-d.arg[0]-1);
			strs[n].emplace(dict_get(d.rel), d.fname ?
				file_read_text(str) : str);
		}
		set<matrix> s;
		for (auto x : rp.p[n].r) {
			ar = max(ar, x.h.e.size());
			for (auto e:x.h.e) if (e.type==elem::SYM) dict_get(e.e);
			for (auto y : x.b) {
				ar = max(ar, y.e.size());
				for (auto e:y.e)
					if (e.type==elem::SYM) dict_get(e.e);
			}
		}
	}
	++ar;
	for (size_t n = 0; n != rp.p.size(); ++n) {
		progs.emplace_back(new lp(dict_bits(), ar, nsyms())),
		proofs.emplace_back();
		for (auto x : strs[n])
			for (int_t n = 0; n != (int_t)x.second.size(); ++n)
				progs.back()->rule_add(matrix{{ 1, x.first,
					n+(int_t)syms.size(),
					x.second[n]+(int_t)syms.size(),
					n+(int_t)syms.size()+1, pad }});
		for (auto x : rp.p[n].r)
			progs.back()->rule_add(get_rule(x),
				proof ? &proofs.back() : 0);
	}
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
	progs.push_back(q);
	printbdd(wcout, progs.size()-1, add);
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
	return printdb(wcout, progs.size()-1), true;
}

int main(int argc, char** argv) {
	setlocale(LC_ALL, ""), tml_init();
	//parser_test();
	bool proof = argc == 2 && !strcmp(argv[1], "-p");
	driver d(stdin, proof);
	if (!d.pfp(proof)) wcout << "unsat" << endl;
	return 0;
}
