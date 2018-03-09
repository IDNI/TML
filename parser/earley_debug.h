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

void print_grammar(const std::vector<std::vector<const wchar_t*>>& g) {
	for (auto& r : g) {
		std::wcout << r[0] << "\t => ";
		if (r.size() == 1) std::wcout << L"ε ";
		else for (size_t i = 1; i < r.size(); ++i)
			if (wcslen(r[i])) std::wcout << r[i] << L' ';
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
