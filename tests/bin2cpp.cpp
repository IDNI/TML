// converts file into binary c string usable for expected data in archive test

#include <iomanip>
#include <iostream>

using namespace std;

int main() {
	stringstream ss; ss << cin.rdbuf();
	string s = ss.str();
	cout << "size_t data_length = " << s.size() << ";\n";
	cout << "unsigned char data[] = \n\"";
	cout << hex << setfill('0');
	size_t n = 0;
	for (unsigned char ch : s) {
		if (n && !(n % 16))     cout << "\"\n\"";
		if (!(n % 8) && n % 16) cout << "\" \"";
		cout << "\\x" << setw(2) << (int)ch  << setw(1);
		++n;
	}
	cout << "\";" << endl;
}
