// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.
#include "repl.h"

using namespace std;

repl::repl(options &o, wostream& os) : o(o), os(os) {
	os<<L"# TML REPL ("<<GIT_DESCRIBED<<L"). Enter ? or h for help."<<endl;
	redrive();
	loop();
}

void repl::redrive(wstring src) {
	fin = false;
	if (d) free(d);
	d = src == L"" ? new driver(o) : new driver(src, o);
}

void repl::restart() {
	d->restart();
	os << L"# Restarted" << endl;
}

void repl::reparse() {
	wstringstream ss;
	d->list(ss);
	redrive(ss.str());
	os << L"# Reparsed" << endl;
}

void repl::reset() {
	redrive();
	os << L"# Reset" << endl;
}

void repl::run(size_t steps, size_t break_on_step, bool break_on_fp) {
	os << L"# Running";
	if (steps) os << L" " << steps << L" step" << (steps==1?L"":L"s");
	if (break_on_step) os << L", break on step: "<<break_on_step;
	if (break_on_fp) os << L", break on fixed point";
	os << endl;

	if (!fin) fin = d->run(steps, break_on_step, break_on_fp);
	if (ap) d->out(os);
}

void repl::add(wstring line) {
	os<<L"# Adding '"<<line<<L"'"<<(ils?L" as a sequence":L"")<<endl;
	fin = false;
	d->add(line, ils);
	if (ar) run();
}

void repl::dump() {
	os<<L"# Dumping to '"<<o.get_string(L"dump")<<L"'"<<endl;
	static wostream& os = output::to(L"dump");
	d->out(os);
}

void repl::info() {
	d->info(os);
	os<<L"# auto run: "<<ar<<L"\tauto print: "<<ap<<L"\tauto info: "<<ai
		<<endl;
}

void repl::print() {
	d->out(os << L"# Printing database content:" << endl);
}

void repl::list(size_t p) {
	d->list(os, p);
}

size_t parse_size_t(wstring l, wstring cmd) {
	try {
		if (l.rfind(cmd, 0) == 0 && l[cmd.size()] == L' ')
			return stoi(wstring(l.begin()+cmd.size()+1, l.end()));
	} catch (...) { }
	return 0;
}

void repl::loop() {
	static wstring ll = L"";
	wstring l;
	while (wcin) {
		os << endl << L"?- ";
		getline(wcin, l);
		if (l == L"") os<<L"# Repeating: '"<<(l = ll)<<L"'"<<endl;
		else          ll = l;
		if       (l == L"restart") restart();
		else if  (l == L"reparse") reparse();
		else if  (l == L"reset")   reset();
		else if  (l == L"q")   break; // quit
		else if ((l == L"?") ||
			 (l == L"h"))  help();
		else if  (l == L"p")   print();
		else if  (l == L"i") { info(); continue; }
		else if  (l == L"ar")  toggle(L"auto run",   ar);
		else if  (l == L"ap")  toggle(L"auto print", ap);
		else if  (l == L"ai")  toggle(L"auto info",  ai);
		else if  (l == L"ils") toggle(L"input line sequencing", ils);
		else if  (l == L"gc")  bdd::gc();
		else if  (l == L"d")   dump();
		else if ((l == L"c") ||
			 (l == L"r"))  run();
		else if  (l == L"l")   list();
		else if  (size_t p =   parse_size_t(l, L"l")) list(p);
		else if  (l == L"s")   step();
		else if  (size_t s =   parse_size_t(l, L"s")) step(s);
		else if  (l == L"b")   break_on_fp();
		else if  (size_t s =   parse_size_t(l, L"b")) break_on_step(s);
		else
			add(l);
		if (ai) info();
		os << L"# " << (fin ? L"finished " : L"") << L"ok" << endl;
		fin = false;
	}
	if (d) free(d);
}

void repl::help() const {
	os << L"# Commands:\n"
		<< L"#\t?, h    - help\n"
		<< L"#\ti       - info\n"
		<< L"#\tp       - print database\n"
		<< L"#\tl       - list programs\n"
		<< L"#\tl NUM   - list program NUM (1st program = 1)\n"
		<< L"#\tr, c    - run/continue\n"
		<< L"#\ts       - run pfp step\n"
		<< L"#\ts NUM   - run NUM pfp steps\n"
		<< L"#\td       - dump db (to the dump output)\n"
		<< L"#\tgc      - bdd garbage collection\n"
		<< L"#\tar      - toggle auto run\n"
		<< L"#\tap      - toggle auto print\n"
		<< L"#\tai      - toggle auto info\n"
		<< L"#\tils     - toggle input line sequencing\n"
		<< L"#\tb       - run and break on fixed point\n"
		<< L"#\tb NUM   - run and break on NUM step\n"
		<< L"#\treparse - reparses the program\n"
		<< L"#\trestart - restarts the program\n"
		<< L"#\treset   - resets repl (clears the entered program)\n"
		<< L"#\tq       - quit" << endl;
}

void repl::toggle(const wstring& name, bool &setting) {
	setting = !setting;
	os << L"# Changed '" << name << "' to "
		<< (setting ? "true" : "false") << endl;
}
