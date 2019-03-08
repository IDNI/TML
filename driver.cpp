#include "tml.h"
#include <map>
#include <set>
#include <string>
#include <sstream>
using namespace std;

#define er(x)	perror(x), exit(0)
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

typedef wchar_t* wstr;
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

class driver {
	int_t str_read(wstr *s); // parse a string and returns its dict id
	term term_read(wstr *s); // read raw term (no bdd)
	matrix rule_read(wstr *s); // read raw rule (no bdd)
	matrix from_bits(size_t x, size_t bits, size_t ar);
	lp p;
public:
	void prog_read(wstr s);
	bool pfp() { bool r = p.pfp(); return printdb(wcout), r; }
	void printdb(wostream& os) { out(os, p.db, p.bits, p.ar); }
	wostream& out(wostream& os, size_t db, size_t bits, size_t ar);
};

matrix driver::from_bits(size_t x, size_t bits, size_t ar) {
	vbools s = p.allsat(x);
	matrix r(s.size());
	for (term& v : r) v = term(ar, 0);
	size_t n = s.size(), i, b;
	while (n--)
		for (i = 0; i != ar; ++i)
			for (b = 0; b != bits; ++b)
				if (s[n][i * bits + b])
					r[n][i] |= 1 << (bits - b - 1);
	return r;
}

wostream& driver::out(wostream& os, size_t db, size_t bits, size_t ar) {
	set<wstring> s;
	for (auto v : from_bits(db, bits, ar)) {
		wstringstream ss;
		for (auto k : v)
			if (!k) ss << L"* ";
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
void driver::prog_read(wstr s) {
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
	for (matrix t; !(t = rule_read(&s)).empty(); p.rule_add(t));
	p.compile(dict_bits(), nsyms());
}

int main() {
	setlocale(LC_ALL, ""), bdd_init(), dict_init();
//	test_range();
	driver p;
	wstring s = file_read_text(stdin); // got to stay in memory
	wstr str = wcsdup(s.c_str());
	s.clear();
	p.prog_read(str);
	if (!p.pfp()) wcout << "unsat" << endl;
	return 0;
}
