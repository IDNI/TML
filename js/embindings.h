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
		.property("result", &driver::result)
		.property("opts", &driver::opts)
		;
	class_<options>("options")
		.constructor<>()
		.function("parse", select_overload
			<void(std::vector<std::string>, bool)> (&options::parse))
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
