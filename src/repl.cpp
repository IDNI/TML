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

repl::repl(options &o, ostream_t& os) : o(o), os(os) {
	os<<"# TML REPL ("<<GIT_DESCRIBED<<"). Enter ? or h for help."<<endl;
	redrive("");
	if (o.enabled("udp")) {
		string addr = o.get_string("udp-addr");
		int_t port = o.get_int("udp-port");
		os<<"# listening on "<<addr<<':'<<port<<"/udp"<<endl;
		up_udp = make_unique<udp>(addr, port);
		if (up_udp->error()) {
			o::err() << up_udp->error_message() << endl;
			up_udp = 0;
		}
	}
	loop();
}

template <typename T>
void repl::prompt(basic_ostream<T>& os) {
	os << "\n?- " << flush;
}
template void repl::prompt(basic_ostream<char>&);
template void repl::prompt(basic_ostream<wchar_t>&);

void repl::redrive(const string& src) {
	fin = false;
	d = src == ""
		? make_unique<driver>(o)
		: make_unique<driver>(src, o);
}

template <typename T>
void repl::restart(basic_ostream<T>& os) {
	d->restart();
	os << "# Restarted" << endl;
}
template void repl::restart(basic_ostream<char>& os);
template void repl::restart(basic_ostream<wchar_t>& os);

template <typename T>
void repl::reparse(basic_ostream<T>& os) {
	ostringstream_t ss;
	d->list(ss);
	redrive(ws2s(ss.str()));
	os << "# Reparsed" << endl;
}
template void repl::reparse(basic_ostream<char>&);
template void repl::reparse(basic_ostream<wchar_t>&);

template <typename T>
void repl::reset(basic_ostream<T>& os) {
	redrive("");
	os << "# Reset" << endl;
}
template void repl::reset(basic_ostream<char>&);
template void repl::reset(basic_ostream<wchar_t>&);

template <typename T>
void repl::run(basic_ostream<T>& os, size_t steps, size_t break_on_step)
{
	os << "# Running";
	if (steps) os << " " << steps << " step" << (steps==1?"":"s");
	if (break_on_step) os << ", break on step: "<<break_on_step;
	os << endl;

	if (!fin) fin = d->run(steps, break_on_step);
	if (ap) d->out(os);
}
template void repl::run(basic_ostream<char>&, size_t, size_t);
template void repl::run(basic_ostream<wchar_t>&, size_t, size_t);

template <typename T>
void repl::add(basic_ostream<T>& os, string line) {
	os<<"# Adding '"<<line<<"'"<<(ils?" as a sequence":"")<<endl;
	fin = false;
	inputs *ii = d->get_inputs();
	input *in = ii->add_string(line);
	if (!d->get_current_input()) {
		d->set_current_input(in);
		if (in) d->add(in);
	}
	d->read_inputs();
	if (ar) run(os);
}
template void repl::add(basic_ostream<char>&, string);
template void repl::add(basic_ostream<wchar_t>&, string);

void repl::dump() {
	os<<"# Dumping to '"<<o.get_string("dump")<<"'"<<endl;
	dump(o::dump());
}

template <typename T>
void repl::dump(basic_ostream<T>& os) {
	d->out(os);
}
template void repl::dump(basic_ostream<char>& os);
template void repl::dump(basic_ostream<wchar_t>& os);

template <typename T>
void repl::info(basic_ostream<T>& os) {
	d->info(os);
	os<<"# auto run: "<<ar<<"\tauto print: "<<ap<<"\tauto info: "<<ai
		<<endl;
}
template void repl::info(basic_ostream<char>&);
template void repl::info(basic_ostream<wchar_t>&);

template <typename T>
void repl::print(basic_ostream<T>& os) {
	d->out(os << "# Printing database content:" << endl);
}
template void repl::print(basic_ostream<char>&);
template void repl::print(basic_ostream<wchar_t>&);

template <typename T>
void repl::list(basic_ostream<T>& os, size_t p) {
	d->list(os, p);
}
template void repl::list(basic_ostream<char>&, size_t);
template void repl::list(basic_ostream<wchar_t>&, size_t);

/**
 * parses size_t from a string. if fails returns 0.
 */
size_t parse_size_t(string l, string cmd) {
	int_t r = 0;
	if (l.rfind(cmd, 0) == 0 && l[cmd.size()] == ' ') {
#ifdef WITH_EXCEPTIONS
	try {
#endif
		string s(l.begin() + cmd.size() +1, l.end());
		r = stoll(s);
#ifdef WITH_EXCEPTIONS
	} catch (...) {}
#else
		if (s != to_string_(r)) r = 0;
#endif
	}
	return r;
}

string parse_string(string l, string cmd) {
	if (l.rfind(cmd, 0) == 0 && l[cmd.size()] == ' ')
		return (string(l.begin() + cmd.size() + 1, l.end()));
	return "";
}

void repl::out_dict(wostream& os) {
	ostringstream_t ss;
	d->out_dict(ss);
#ifdef WITH_WCHAR
	os << ss.str();
#else
	os << s2ws(ss.str());
#endif
}
void repl::out_dict(ostream& os) {
	ostringstream_t ss;
	d->out_dict(os);
#ifdef WITH_WCHAR
	os << ws2s(ss.str());
#else
	os << ss.str();
#endif
}

template <typename T>
bool repl::eval_input(basic_ostream<T>& os, string l) {
	static string ll = "";
	string f;
	if (l == "") os<<"# Repeating: '"<<(l = ll)<<"'"<<endl;
	else ll = l;
	if       (l == "restart") restart(os);
	else if  (l == "reparse") reparse(os);
	else if  (l == "reset")   reset(os);
	else if  (l == "dict") {  out_dict(os); return false; }
	else if  (l == "q") return true; // quit
	else if ((l == "?") ||
		(l == "h"))  help(os);
	else if  (l == "p")   print(os);
	else if  (l == "i") { info(os); return false; }
	else if  (l == "ar")  toggle(os, "auto run",   ar);
	else if  (l == "ap")  toggle(os, "auto print", ap);
	else if  (l == "ai")  toggle(os, "auto info",  ai);
	else if  (l == "ils") toggle(os, "input line sequencing", ils);
	else if  (l == "gc")  bdd::gc();
	else if  (l == "d")   dump(os);
	else if ((l == "c") ||
		(l == "r"))  run(os);
	else if  (l == "l")   list(os);
	else if  (size_t p =   parse_size_t(l, "l")) list(os, p);
	else if  (l == "s")   step(os);
	else if  (size_t s =   parse_size_t(l, "s")) step(os, s);
	else if  (size_t s =   parse_size_t(l, "b")) break_on_step(os, s);
	else if  (l == "ps")
		d->set_print_step(toggle(os, "print steps", ps));
	else if  (l == "pu")
		d->set_print_updates(toggle(os, "print updates", pu));
	else if  (l == "cu")
		d->set_populate_tml_update(
			toggle(os, "collect updates into tml_update", cu));
	else
		add(os, l);
	if (ai) info(os);
	os << "# " << (fin ? "finished " : "") << "ok" << endl;
	fin = false;
	return false;
}
template bool repl::eval_input(basic_ostream<char>&, string);
template bool repl::eval_input(basic_ostream<wchar_t>&, string);


template <typename T>
void repl::help(basic_ostream<T>& os) const {
	os << "# Commands:\n"
		<< "#\t?, h    - help\n"
		<< "#\ti       - info\n"
		<< "#\tp       - print database\n"
		<< "#\tl       - list programs\n"
		<< "#\tl NUM   - list program NUM (1st program = 1)\n"
		<< "#\tr, c    - run/continue\n"
		<< "#\ts       - run pfp step\n"
		<< "#\ts NUM   - run NUM pfp steps\n"
		<< "#\td       - dump db (to the dump output)\n"
		<< "#\tdict    - print internal string dictionary\n"
		<< "#\tgc      - bdd garbage collection\n"
		<< "#\tcu      - toggle collect updates\n"
		<< "#\tps      - toggle print steps\n"
		<< "#\tpu      - toggle print updates\n"
		<< "#\tar      - toggle auto run\n"
		<< "#\tap      - toggle auto print\n"
		<< "#\tai      - toggle auto info\n"
		<< "#\tils     - toggle input line sequencing\n"
		<< "#\tb       - run and break on fixed point\n"
		<< "#\tb NUM   - run and break on NUM step\n"
		<< "#\treparse - reparses the program\n"
		<< "#\trestart - restarts the program\n"
		<< "#\treset   - resets repl (clears the entered program)\n"
		<< "#\tq       - quit" << endl;
}
template void repl::help(basic_ostream<char>&) const;
template void repl::help(basic_ostream<wchar_t>&) const;

template <typename T>
bool repl::toggle(basic_ostream<T>& os, const string& name, bool &setting) {
	setting = !setting;
	os << "# Changed '" << name << "' to "
		<< (setting ? "true" : "false") << endl;
	return setting;
}
template bool repl::toggle(basic_ostream<char>&, const string&, bool &);
template bool repl::toggle(basic_ostream<wchar_t>&, const string&, bool &);

void repl::loop() {
	string input;
	prompt(os);
	for (;;) {
		input = {};
		if (CIN && in_reader.readable()) {
			input = ws2s(in_reader.read());
			if (input.size()) {
				if (eval_input(input)) break;
				prompt(os);
			}
		}
		if (up_udp && up_udp->readable()) {
			udp_message msg = up_udp->read();
			input = msg.second;
			if (!input.empty()) input.pop_back(); // remove \n
			stringstream ss;
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
		this_thread::sleep_for(chrono::milliseconds(20));
	}
}
