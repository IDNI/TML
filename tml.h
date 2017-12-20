#include <vector>
#include <map>
#include <set>
#include <cstring>
#include <cstdint>
#include <iostream>
#include <algorithm>
#include "strings.h"
#include "clause.h"
using std::vector;
using std::map;
using std::set;
using std::wstring;
using std::wstringstream;
using std::wcout;
using std::wcin;
using std::wcerr;
using std::wistream;
using std::wostream;
using std::pair;
using std::endl;
using std::runtime_error;

class dlp : protected vector<const clause*> { // disjunctive logic program
	typedef map<int32_t, map<size_t, size_t>> index_t;
	index_t index;
	void program_read(strbuf&);
public:
	void program_read(wistream&);
	void pe(clause&);
	void index_write(wostream&) const;
	uint64_t hash;
	friend wostream& operator<<(wostream&, const dlp&);
	dlp& operator+=(clause*);
	virtual ~dlp();
};

wostream& operator<<(wostream &os, const env &e);
