#include "literal.h"
#include "strings.h"
#include <iostream>

class clause : protected vector<literal*> {
	typedef vector<literal*> base;
public:
	clause() {}
	clause(const clause&, env&);

	static clause* clause_read(strbuf&);
	static clause* clause_read(std::wistream&);

	uint64_t hash = 0;
	uint64_t rehash();
	void sort();
	bool add(const literal&);
	void flip();
	void clear();
	literal *unit() const;
	clause& operator+=(const literal&);

	size_t size() const;
	int32_t lastrel() const;
	const literal* at(size_t k) const;
	friend wostream& operator<<(wostream &os, const clause&);
	bool operator==(const clause&) const;
	virtual ~clause();
};

