#include <map>
#include <set>

template<typename T>
struct dig { // digraph
	size_t sz = 0;
	std::map<T, std::set<T>> in, out;
};

template<typename T> void add(dig<T>& d, const T& x, const T& y) {
	if (d.out[x].emplace(y).second) d.in[y].emplace(x), ++d.sz;
}
template<typename T> bool has(const dig<T>& d, const T& x, const T& y) {
	auto it = d.out.find(x);
	return it != d.out.end() && has(it->second, y);
}
template<typename S> bool have_common(const S& x, const S& y) {
	for (auto ix=x.begin(),iy=y.begin();ix!=x.end()&&iy!=y.end();)
		if (*ix < *iy) ++ix;
		else if (*ix > *iy) ++iy;
		else return true;
	return false;
}
template<typename X, typename Y, typename Z>
void close(const X &in, const Y &out, Z &res) {
	for (size_t s = 0; s != res.sz;) {
		s = res.sz;
		for (const auto& x : out)
			for (const auto& y : in)
				if (have_common(x.second, y.second))
					add(res, x.first, y.first);
	}
}
