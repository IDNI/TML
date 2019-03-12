#include "defs.h"
#include <vector>
#include <array>

#define dot_expected "'.' expected.\n"
#define sep_expected "Term or ':-' or '.' expected.\n"
#define unmatched_quotes "Unmatched \"\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"
#define err_quotes "expected \".\n"
#define err_dots "two consecutive dots, or dot in beginning of document.\n"
#define err_quote "' should come before and after a single character only.\n"
#define err_fname "malformed filename.\n"
#define err_directive_arg "invalid directive argument.\n"
#define err_escape "invalid escaped character\n"
#define err_int "malformed int.\n"
#define err_lex "lexer error (please report as a bug).\n"
#define err_parse "parser error (please report as a bug).\n"
#define err_chr "unexpected character.\n"
#define err_body "rules' body expected.\n"
#define err_term_or_dot "term or dot expected.\n"

typedef const wchar_t* cws;
typedef cws* pcws;

typedef std::array<cws, 2> lexeme;
typedef std::vector<lexeme> lexemes;
