#include <cassert>
#include <algorithm>
#include <vector>
#include <functional>
#include <unordered_map>
#include <iostream>

template<typename K, typename V>
class hmap {
	struct item {
		K k;
		V v;
		bool operator<(const K& t) const { return k < t; }
	};
	std::vector<std::vector<item>> M;
	std::hash<K> h;
	size_t bits = 2;
public:
	hmap() { M.resize(4); }
	void clear() { M.clear(), M.resize(4), bits = 2; }
	const V* find(const K& k) const {
		auto &b = M[h(k) & ((1 << bits) - 1)];
		auto it = std::lower_bound(b.begin(), b.end(), k);
		return it != b.end() && it->k == k ? &it->v : 0;
	}
	const V put(const K& k, const V& v) {
		auto &b = M[h(k) & ((1 << bits) - 1)];
		auto it = std::lower_bound(b.begin(), b.end(), k);
		if (it == b.end() || it->k != k) {
			b.insert(it, { k, v });
			if (b.size() >= 16) rebuild();
			return v;
		}
		return it->v;
	}
	void del(const K& k) {
		auto &b = M[h(k) & ((1 << bits) - 1)];
		auto it = std::lower_bound(b.begin(), b.end(), k);
		if (it != b.end() && it->k == k) b.erase(it);
	}
	void rebuild() {
		std::wcerr << "rebuild " << M.size() << std::endl;
		std::vector<std::vector<item>> v(1 << ++bits);
		for (auto &x : M)
			for (auto &y : x) {
				auto &b = v[h(y.k) & ((1 << bits) - 1)];
				b.insert(std::lower_bound(b.begin(), b.end(), y.k), y);
			}
		M = move(v);
	}
	template<typename F> void forall(F f) const {
		for (auto x : M) for (auto y : x) f(y.k, y.v);
	}
};
