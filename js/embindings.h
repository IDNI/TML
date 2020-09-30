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
#include <emscripten.h>
#include <emscripten/bind.h>
#include "../src/driver.h"

using
	emscripten::enum_,
	emscripten::class_,
	emscripten::register_vector,
	emscripten::optional_override,
	emscripten::select_overload,
	emscripten::allow_raw_pointers;

EMSCRIPTEN_BINDINGS(tml) {
	enum_<output::type_t>("type_t")
		.value("NONE",   output::type_t::NONE)
		.value("STDOUT", output::type_t::STDOUT)
		.value("STDERR", output::type_t::STDERR)
		.value("FILE",   output::type_t::FILE)
		.value("BUFFER", output::type_t::BUFFER)
		.value("NAME",   output::type_t::NAME)
		;
	enum_<mmap_mode>("mmap_mode")
		.value("MMAP_NONE", mmap_mode::MMAP_NONE)
		.value("MMAP_READ", mmap_mode::MMAP_READ)
		.value("MMAP_WRITE", mmap_mode::MMAP_WRITE)
		;
	class_<bdd>("bdd")
		.class_function("init", &bdd::init)
		.class_function("gc", &bdd::gc)
		;
	class_<driver>("driver")
		.constructor<std::string, options>(allow_raw_pointers())
		.class_function("create",// cptr = WA/HEAP const char* with UTF8 
			optional_override([](int_t cptr, options o) {
				const char *prog =
					reinterpret_cast<const char*>(cptr);
				return new driver(prog, o);
			}), allow_raw_pointers())
		.function("out", optional_override(
			[](driver& self, emscripten::val v) {
				return self.out(v);
			}
		))
		.function("dump", &driver::dump)
		.function("info", &driver::info<syschar_t>)
		.function("list", &driver::list<syschar_t>)
		.function("add", &driver::add, allow_raw_pointers())
		.function("restart", &driver::restart)
		.function("run", &driver::run)
		.function("step", &driver::step)
		.function("nsteps", &driver::nsteps)
		.function("set_print_step", &driver::set_print_step)
		.function("set_print_updates", &driver::set_print_updates)
		.function("set_populate_tml_update", &driver::set_populate_tml_update)
		.function("out_goals", &driver::out_goals<syschar_t>)
		.function("out_dict", &driver::out_dict<syschar_t>)
		.function("size", &driver::size)
		.function("load", &driver::load)
		.function("save", &driver::save)
		//.function("db_size", &driver::db_size)
		.function("db_load", &driver::db_load)
		.function("db_save", &driver::db_save)
		.property("result", &driver::result)
		.property("error", &driver::error)
		.property("opts", &driver::opts)
		;
	class_<options>("options")
		.constructor<strings, inputs*, outputs*>()
		.function("parse", select_overload
			<void(std::vector<std::string>, bool)>
				(&options::parse), allow_raw_pointers())
		.function("enabled", &options::enabled)
		.function("get", &options::get)
		.function("get_int", &options::get_int)
		.function("get_bool", &options::get_bool)
		.function("get_string", &options::get_string)
		.function("to_string", optional_override([](options& o) {
			ostringstream_t ss; ss << o;
			return ss.str();
		}), allow_raw_pointers())
		;
	class_<inputs>("inputs")
		.constructor<>()
		.class_function("ref", optional_override([](inputs &ii) {
				return &ii;
			}), allow_raw_pointers())
		;
	class_<output>("output")
		.function("name", &output::name)
		.function("type", &output::type)
		//.function("os", &output::os)
		.function("target", select_overload<std::string()const>(&output::target), allow_raw_pointers())
		.function("read", &output::read)
		.function("is_null", &output::is_null)
		.class_function("create", &output::create)
		.class_function("get_type", &output::get_type)
		.class_function("type_name", &output::type_name)
		;
	class_<outputs>("outputs")
		.constructor<>()
		.class_function("ref", optional_override([](outputs &oo) {
				return &oo;
			}), allow_raw_pointers())
		.function("use", &outputs::use)
		.function("add", &outputs::add)
		.class_function("read", &outputs::read)
		.class_function("in_use", &outputs::in_use, allow_raw_pointers())
		//.class_function("out", &outputs::out)
		//.class_function("err", &outputs::err)
		//.class_function("inf", &outputs::inf)
		//.class_function("dbg", &outputs::dbg)
		//.class_function("ms", &outputs::ms)
		//.class_function("dump", &outputs::dump)
		.class_function("get", &outputs::get, allow_raw_pointers())
		//.class_function("to", &outputs::to)
		.class_function("exists", &outputs::exists)
		.class_function("target", &outputs::target)
		;
	register_vector<std::string>("strings");
};

EM_JS(void, console_log, (std::string msg), {
	console.log('console_log(from C++):', msg);
});
