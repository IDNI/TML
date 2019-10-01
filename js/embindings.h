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
using
	emscripten::class_,
	emscripten::register_vector,
	emscripten::optional_override,
	emscripten::select_overload,
	emscripten::allow_raw_pointers;

EMSCRIPTEN_BINDINGS(tml) {
	class_<bdd>("bdd")
		.class_function("init", &bdd::init)
		.class_function("gc", &bdd::gc)
		;
	class_<driver>("driver")
		.class_function("init", &driver::init)
		.class_function("create",
			optional_override([](std::wstring s, options o) {
				return new driver(s, o);
			}), allow_raw_pointers())
		.function("out", select_overload
			<void(emscripten::val)const> (&driver::out))
		.function("to_bin", &driver::to_bin)
		.property("result", &driver::result)
		.property("opts", &driver::opts)
		;
	class_<options>("options")
		.constructor<>()
		.function("parse", select_overload
			<void(std::vector<std::string>, bool)>
				(&options::parse))
		.function("enabled", &options::enabled)
		.function("get", &options::get)
		.function("get_int", &options::get_int)
		.function("get_bool", &options::get_bool)
		.function("get_string", &options::get_string)
		.function("to_string", optional_override([](options& o) {
			std::wstringstream wss; wss << o;
			return wss.str();
		}))
		;
	class_<output>("output")
		.class_function("read", &output::read)
		;
	register_vector<std::string>("strings");
};
