#include "earley.h"

using namespace std;

int main(int, char**) {
	setlocale(LC_ALL, "");
	wstring S(L"S"), T(L"T"), B(L"B"), a(L"a"), b(L"b"), ws(L"ws"), eps,
		A(L"A");
//	cfg g({ { S, a, S }, { S/*, eps*/ }}, S);
//	cfg &g = *cfg_create({ { S, a, S }, {S, a, eps} }, S);
	cfg &g = *cfg_create({ { S, S, T }, { S, a }, { B, eps }, { T, a, b },
		{ T, a } }, S.c_str());
	cfg_parse(g, L"aa");
	cfg_delete(&g);
	return 0;
}
