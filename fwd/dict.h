#ifndef __DICT_H__
#define __DICT_H__
class dict_t {
	map<wstring, int_t> m;
	vector<wstring> v;
public:
	dict_t() { m.emplace(L"not", 0); }
	int_t operator()(const wstring& s) {
		assert(s.size());
		if (auto it = m.find(s); it != m.end()) return it->second;
		v.push_back(s);
		return m.emplace(s,s[0]==L'?'?-v.size():v.size()).first->second;
	}
	wstring operator()(int_t x) const {
		return x > 0 ? v[x - 1] : x ? L"v"s+to_wstring(-x) : L"not";
	}
	int_t tmp(wstring prefix = L"_") {
		wstring s;
		for (size_t n = 1;;++n) {
			wstring s = prefix + to_wstring(n);
			if (m.find(s) == m.end()) return (*this)(s);
		}
	}
};

extern dict_t dict;
#endif
