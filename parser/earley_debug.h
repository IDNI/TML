#include <iostream>
#include <sstream>
#include <iomanip>

std::wstring dr2str(const cfg& G, size_t d) {
	const auto& g = G.g;
	const std::vector<std::wstring>& r = g[d / G.w];
	std::wstringstream ss;
	ss<<std::setw(3)<<d<<" "; if(!(d%G.w)) ss<<"* ";ss<<L'['<<r[0]<<" => ";
	for(size_t n=1;n<r.size();++n) {
		if (n == d%G.w) ss << "* ";
		if (r[n].size()) ss << r[n] <<L' ';
		else ss << L"ε ";
	}
	if (r.size() == d % G.w) ss << "* ";
	return ss << L']', ss.str();
}

std::wstring ei2str(const cfg& G, size_t i) {
	std::wstringstream ss;
	ss << std::setw(4) << i << " {" << std::left << std::setw(G.w*4)
	   << dr2str(G,i/G.len);
	return ss << ',' << i % G.len << " }", ss.str();
}

std::wstring es2str(const cfg& G, size_t s) {
	std::wstringstream ss;
	for (size_t i : G.ep[s])ss<<"P[" << s << "]: "<<ei2str(G, i)<<std::endl;
	for (size_t i : G.ec[s])ss<<"C[" << s << "]: "<<ei2str(G, i)<<std::endl;
//	for (	auto it = G.ep.out.lower_bound(s), e = G.ep.out.upper_bound(s);
//		it != e && it->first < s+G.len; ++it)
//		ss<<"P[" << s << "]: "<<ei2str(G, it->first/G.len)<<std::endl;
//	for (	auto it = G.ec.out.lower_bound(s), e = G.ec.out.upper_bound(s);
//		it != e && it->first < s+G.len; ++it)
//		ss<<"P[" << s << "]: "<<ei2str(G, it->first/G.len)<<std::endl;
	return ss.str();
}

void print_cache(const cfg& G, const dig<size_t>& d) {
	for (const auto& x : d.out) {
		std::wcout << std::left << std::setw(G.w*4)
			   << dr2str(G, x.first) << "\t=>\t";
		for (auto y : x.second)
			std::wcout << std::left << std::setw(G.w*4)
				   << dr2str(G,y)<<" ";
		std::wcout << std::endl;
	}
	std::wcout << std::endl;
}

void print_grammar(const std::vector<std::vector<std::wstring>>& g) {
	for (auto& r : g) {
		std::wcout << r[0] << "\t => ";
		if (r.size() == 1) std::wcout << L"ε ";
		else for (size_t i = 1; i < r.size(); ++i)
			if (r[i].size()) std::wcout << r[i] << L' ';
			else std::wcout << L"ε ";
		std::wcout << std::endl;
	}
	std::wcout << std::endl;
}

void print_nullables(const std::set<std::wstring>& nulls) {
	std::wcout << "nullables: ";
	for (const std::wstring& d : nulls)
		if (d.size()) std::wcout<<d<<' '; else std::wcout<<L"ε ";
	std::wcout << std::endl;
}
