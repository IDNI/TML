typedef int64_t int_t;
typedef wchar_t* wstr;
typedef std::vector<int_t> term;
typedef std::vector<term> matrix;// set of relational terms
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;
//#define DEBUG
#ifdef DEBUG
#define DBG(x) x
#else
#define DBG(x)
#endif
