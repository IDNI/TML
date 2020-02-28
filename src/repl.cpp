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
#include <chrono>
#include <thread>

#include "repl.h"

using namespace std;

repl::repl(options &o, wostream& os) : o(o), os(os) {
	os<<L"# TML REPL ("<<GIT_DESCRIBED<<L"). Enter ? or h for help."<<endl;
	redrive();
	if (o.enabled(L"udp")) {
		wstring addr = o.get_string(L"udp-addr");
		int_t port = o.get_int(L"udp-port");
		os<<L"# listening on "<<addr<<L':'<<port<<L"/udp"<<endl;
		up_udp = make_unique<udp>(ws2s(addr), port);
		if (up_udp->error()) {
			o::err() << up_udp->error_message() << endl;
			up_udp = 0;
		}
	}
	loop();
}

void repl::prompt(wostream& os) {
	os << L"\n?- " << std::flush;
}

void repl::redrive(wstring src) {
	fin = false;
	if (d) free(d);
	d = src == L"" ? new driver(o) : new driver(src, o);
}

void repl::restart(wostream& os) {
	d->restart();
	os << L"# Restarted" << endl;
}

void repl::reparse(wostream& os) {
	wstringstream ss;
	d->list(ss);
	redrive(ss.str());
	os << L"# Reparsed" << endl;
}

void repl::reset(wostream& os) {
	redrive();
	os << L"# Reset" << endl;
}

void repl::run(wostream& os, size_t steps, size_t break_on_step,
	bool break_on_fp)
{
	os << L"# Running";
	if (steps) os << L" " << steps << L" step" << (steps==1?L"":L"s");
	if (break_on_step) os << L", break on step: "<<break_on_step;
	if (break_on_fp) os << L", break on fixed point";
	os << endl;

	if (!fin) fin = d->run(steps, break_on_step, break_on_fp);
	if (ap) d->out(os);
}

void repl::add(wostream& os, wstring line) {
	os<<L"# Adding '"<<line<<L"'"<<(ils?L" as a sequence":L"")<<endl;
	fin = false;
	d->add(line, ils);
	if (ar) run(os);
}

void repl::dump() {
	os<<L"# Dumping to '"<<o.get_string(L"dump")<<L"'"<<endl;
	dump(o::dump());
}

void repl::dump(wostream& os) {
	d->out(os);
}

void repl::info(wostream& os) {
	d->info(os);
	os<<L"# auto run: "<<ar<<L"\tauto print: "<<ap<<L"\tauto info: "<<ai
		<<endl;
}

void repl::print(wostream& os) {
	d->out(os << L"# Printing database content:" << endl);
}

void repl::list(wostream&os, size_t p) {
	d->list(os, p);
}

size_t parse_size_t(wstring l, wstring cmd) {
	try {
		if (l.rfind(cmd, 0) == 0 && l[cmd.size()] == L' ')
			return stoi(wstring(l.begin()+cmd.size()+1, l.end()));
	} catch (...) { }
	return 0;
}

bool repl::eval_input(wostream& os, wstring &l) {
	static wstring ll = L"";
	if (l == L"") os<<L"# Repeating: '"<<(l = ll)<<L"'"<<endl;
	else          ll = l;
	if       (l == L"restart") restart(os);
	else if  (l == L"reparse") reparse(os);
	else if  (l == L"reset")   reset(os);
	else if  (l == L"dict") {  d->out_dict(os); return false; }
	else if  (l == L"q")   return true; // quit
	else if ((l == L"?") ||
			(l == L"h"))  help(os);
	else if  (l == L"p")   print(os);
	else if  (l == L"i") { info(os); return false; }
	else if  (l == L"ar")  toggle(os, L"auto run",   ar);
	else if  (l == L"ap")  toggle(os, L"auto print", ap);
	else if  (l == L"ai")  toggle(os, L"auto info",  ai);
	else if  (l == L"ils") toggle(os, L"input line sequencing", ils);
	else if  (l == L"gc")  bdd::gc();
	else if  (l == L"d")   dump(os);
	else if ((l == L"c") ||
			(l == L"r"))  run(os);
	else if  (l == L"l")   list(os);
	else if  (size_t p =   parse_size_t(l, L"l")) list(os, p);
	else if  (l == L"s")   step(os);
	else if  (size_t s =   parse_size_t(l, L"s")) step(os, s);
	else if  (l == L"b")   break_on_fp(os);
	else if  (size_t s =   parse_size_t(l, L"b")) break_on_step(os, s);
	else if  (l == L"ps")
		d->set_print_step(toggle(os, L"print steps", ps));
	else if  (l == L"pu")
		d->set_print_updates(toggle(os, L"print updates", pu));
	else if  (l == L"cu")
		d->set_populate_tml_update(
			toggle(os, L"collect updates into tml_update", cu));
	else
		add(os, l);
	if (ai) info(os);
	os << L"# " << (fin ? L"finished " : L"") << L"ok" << endl;
	fin = false;
	return false;
}

void repl::help(wostream& os) const {
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
		<< L"#\tdict    - print internal string dictionary\n"
		<< L"#\tgc      - bdd garbage collection\n"
		<< L"#\tcu      - toggle collect updates\n"
		<< L"#\tps      - toggle print steps\n"
		<< L"#\tpu      - toggle print updates\n"
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

bool repl::toggle(wostream& os, const wstring& name, bool &setting) {
	setting = !setting;
	os << L"# Changed '" << name << "' to "
		<< (setting ? "true" : "false") << endl;
	return setting;
}

void repl::loop() {
	wstring input;
	prompt(os);
	for (;;) {
		input = {};
		if (wcin && wcin_reader.readable()) {
			input = wcin_reader.read();
			if (input.size()) {
				if (eval_input(input)) break;
				prompt(os);
			}
		}
		if (up_udp && up_udp->readable()) {
			udp_message msg = up_udp->read();
			input = s2ws(msg.second);
			if (!input.empty()) input.pop_back(); // remove \n
			wstringstream ss;
			bool br = eval_input(ss, input);
			// TODO split responses bigger than BUFLEN
			if (ss.str().size()) {
				prompt(ss);
				up_udp->send(udp_message{
					msg.first,
					ws2s(ss.str())
				});
			}
			if (br) break;

		}
		std::this_thread::sleep_for(std::chrono::milliseconds(20));
	}
	if (d) free(d);
}
