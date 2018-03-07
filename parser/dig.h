#include <map>
#include <set>

template<typename T>
class dig { // digraph
	template<typename S> bool have_common(const S& x, const S& y) {
		for (auto ix=x.begin(),iy=y.begin();ix!=x.end()&&iy!=y.end();)
			if(*ix<*iy)++ix;else if(*ix>*iy)++iy; else return true;
		return false;
	}
public:
	std::map<T, std::set<T>> in, out;
	size_t sz = 0;
	void add(const T& x, const T& y) {
		if (out[x].emplace(y).second) in[y].emplace(x), ++sz;
	}
	bool has(const T& x, const T& y) const {
		auto it = out.find(x);
		return it != out.end() && has(it->second, y);
	}
	void close() {
		for (size_t s = 0; s != sz;) {
			s = sz;
			for (const auto& x : out)
				for (const auto& y : in)
					if (have_common(x.second, y.second))
						add(x.first, y.first);
		}
	}
};
