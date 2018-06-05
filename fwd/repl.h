#include "fwd.h"
#include "dict.h"

class repl {
	fwd p;
	const int_t ifword, thenword;
	wstring get_line() const;
	bool walnum(wchar_t ch) const;
	int_t peek_word(const wchar_t* s) const;
	int_t get_word(const wchar_t** s) const;
	term get_term(const wchar_t** line) const;
	clause get_clause(const wchar_t** line);
	void parse(const wchar_t* line);
public:
	repl();
	void run();
};
