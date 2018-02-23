// some generic formatting templates

template<typename T> wostream& operator<<(wostream& os, const vector<T>& t);
template<typename T> wostream& operator<<(wostream& os, const set<T>& t);
template<typename K, typename V>
wostream& operator<<(wostream& os, const map<K, V>& t);
template<typename T, typename V>
wostream& operator<<(wostream& os, const pair<T, V>& t);

template<typename T, size_t... is>
void print_tuple(wostream& os, const T &t, index_sequence<is...>) {
	((os << (is ? L", " : L"") << get<is>(t)), ...);
} 

template<class... args>
wostream& operator<<(wostream& os, const tuple<args...>& t) {
	os<<L"[ ", print_tuple(os, t, index_sequence_for<args...>{}),os<<L" ] ";
	return os;
}

template<typename T> wostream& operator<<(wostream& os, const vector<T>& t) {
	os << L"( ";
	auto it = t.begin();
	os << *it++;
	while (it != t.end()) os << L' ' << *it++;
	return os << L" ) ";
}

template<typename T> wostream& operator<<(wostream& os, const set<T>& t) {
	os << L"{ ";
	auto it = t.begin();
	os << *it++;
	while (it != t.end()) os << L", " << *it++;
	return os << L" } ";
}

template<typename K, typename V>
wostream& operator<<(wostream& os, const map<K, V>& t) {
	for (auto&& [k, v] : t) os << k << L" -> " << v << endl;
	return os;
}

template<typename T, typename V>
wostream& operator<<(wostream& os, const pair<T, V>& t) {
	return os << L'(' << t.first << L", " << os << t.second << L')';
}
