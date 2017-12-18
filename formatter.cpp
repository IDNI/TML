#include "tml.h"

wostream& operator<<(wostream &os, const env &e) {
	for (const pair<int32_t, int32_t> &x : e)
		(os << dict[x.first] << L'=' << dict[x.second] << L' ').flush();
	os.flush();
	return os;
}

wostream& operator<<(wostream &os, const dict_t &d) {
	for (size_t n = 0; n < d.strings.size(); ++n)
		(os << n+1 << L'\t' << d.strings[n] << endl).flush();
	return os;
}

wostream& operator<<(wostream &os, const literal &l) {
	if (!l[0]) os << dict[l[1]] << L'=' << dict[l[2]];
	else {	os << dict[l[0]] << L'(';
		if (l.size() > 1) os << dict[l[1]];
		for (size_t n = 2; n < l.size(); ++n) os << L',' << dict[l[n]];
		(os << L')' << L'[' << l.h.h << L']').flush();
	}
	return os;
}

wostream& operator<<(wostream &os, const clause &c) {
	for (const literal *l : c) if (l->rel() <=0) os << *l << L' ';
	os << L" -> ";
	for (const literal *l : c) if (l->rel() > 0) os << *l << L' ';
	(os << L'.' << L'[' << c.h.h << L']').flush();
	return os;
}

void dlp::index_write(wostream &os) const {
	for (auto x : index) {
		os << x.first << L':';
		for (auto y : x.second) os<<y.first<<','<<y.second<<L' ';
		(os << endl).flush();
	}
}

wostream& operator<<(wostream &os, const dlp& p) {
	for (const clause *c : p) (os << *c << endl).flush();
	return os;
}
