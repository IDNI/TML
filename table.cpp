#include "dnf.h"
#include "pfp.h"
#include <vector>

table::table(size_t cols, size_t bits, size_t offset, int_t rel) :
		cols(cols), bits(bits), offset(offset), rel(rel) {}
table& table::operator+=(const int_t* t) {
	assert((size_t)*t == cols+1 && abs(t[1]) == -rel);
	return f += ::from_bits(t+2, *t-1, offset, bits), *this;
}
table& table::operator-=(const int_t* t) {
	return f -= ::from_bits(t+2, *t-1, offset, bits), *this;
}
vector<const int_t*> table::from_bits(const clause& c) const {
	const int_t from = offset, len = cols * bits, to = from + len;
	uint64_t z = 0;
	char *p = new char[len];//(char*)alloca(sizeof(char) * len);
	size_t k = 0;
	for (int_t n = from; n < to; ++n)
		if (has(c, n)) p[k++] = 1;
		else if (has(c, -n)) p[k++] = -1;
		else ++z, p[k++] = 0;
	if (z > 63)
		wcout << L"Got more than 2^64-1=18446744073709551615 results (around 2^"
			<< z << L" results)"<<endl, exit(0);
	vector<const int_t*> r;
	r.reserve(1 << z);
	for (uint64_t i = 0; i < (uint64_t)(1 << z); ++i) {
		int_t* t = (int_t*)malloc(sizeof(int_t)*(cols+2));
		r.push_back(t);
		t[0] = cols + 1;
		t[1] = rel;
		k = 0;
		for (int_t n = from-1; n < to-1; ++n)
			switch (p[n-from+1]) {
			case 1:	bit_set(t+2, n, bits); break;
			case-1:	bit_unset(t+2, n, bits); break;
			default:(i & (1 << k++)) ? bit_set(t+2, n, bits) : bit_unset(t+2, n, bits);
			}
	}
	return delete[] p, r;
}

wostream& operator<<(wostream& os, const table& t) {
	for (const clause& c : t.f)
		for (const int_t* x : t.from_bits(c))
			os << x;
	return os;
}
