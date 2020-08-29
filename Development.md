# Outputs

`output` is a class wrapping an output stream from TML. It allows to
redirect each of the TML outputs to stdout, stderr, a file, a string
buffer (for reading it later programatically) or to a null.
Outputs are usually configured (targeted) by `options` class.

## creating a new output

Use method `shared_ptr<output> output::create(std::wstring name, std::wstring
target, std::wstring extension);` where all arguments are wstrings.

## targets of outputs

Possible targets are:
- @null
- @stdout
- @stderr
- @buffer
- filename - any string not matching any of above names

## outputs container

There is a container structure for `output` objects.
Pointer to this container is passed to the `options` object which configures the
outputs. Name of the output is matched when a STRING option with the same name
is parsed. More details for configuring outputs see bellow in the *Options*
section.


## default outputs

After creating `outputs` object. You can call its method `init_defaults()` to
create default outputs.

Default outputs are:

|             |                                                   |
| ----------- | ------------------------------------------------- |
| output      | default output for TML print builtins             |
| error       | error messages                                    |
| info        | info messages                                     |
| debug       | debug messages (requires Debug build)             |
| dump        | database dump                                     |
| benchmarks  | measured benchmarks                               |
| transformed | transformed program                               |
| repl-output | repl                                              |
| xsb         | program translated into XSB                       |
| swipl       | program translated into SWIPL                     |
| souffle     | program translated into Soufflé                   |


`outputs` object acts also as a global container. It is possible to use multiple
outputs objects for example when you need to use multiple drivers at the same
time. Switch between `outputs` objects by calling `outputs::use()` or
`o::use(const outputs&)` method.

Example:
```
	outputs oo;
	oo.init_defaults();
	oo.use();
```
This is required when using multiple `outputs` objects.
If there is only a single `outputs` container used in the whole program, calling
`init_defaults()` and `use()` is not necessary since first such object ever
instantiated calls these two methods automatically. It is enough to use just:
```
	outputs oo;
```

## adding new output

Adding new output is possible with calling `outputs::add(shared_ptr<output>)`
or directly: `outputs::add(output::create(name, target, extension))`

## **o** namespace

There is a namespace `o`  to allow quick access to global streams (global
`outputs` object is the first such object or the one which was set global by
calling `outputs::use()`).

For convenience there are methods with quick access to configured wostreams:
- `o::out()`
- `o::err()`
- `o::inf()`
- `o::dbg()`
- `o::repl()`,
- `o::ms()` - this is for **benchmarks** output
- `o::dump()`

There is also `o::to(const std::wstring&)` to get output's wostream by its name.


# Options

There is an `options` class which is used to pass and parse options for
a TML driver. Its constructor or parse function can take parameters with
`int argc/char* argv`, `strings args` or `wstrings args` API.

If you need `options` to configure `outputs`, use a pointer to the container
in constructor or call `set_outputs(outputs*)` before calling `parse()`.

Example:
```
	outputs oo;
	options opts(&oo, argc, argv);
	driver d(opts);
```
or:
```
	std::vectors<std::string>args{ "--no-dump","--transformed","@stdout" };
	outputs oo;
	driver d(options(&oo, args));
```

## reading options

`options` object has methods for reading values: `enabled()`, `disabled()`,
`get_bool()`, `get_int()`, `get_string()`. All take `const wstring& option_name`
as an argument.

Example:
```
	if (o.enabled(L"help")) help();
	else d.run(o.get_int(L"steps));
```

## available options

Run `tml --help` (or `options::help(const wostream&)` programatically) to see
a help generated from all available options and their descriptions.


## adding a new option

Add a new option in the method `void options::setup()`. See its content for
examples.
There is a function `add` adding an option defined by type, names (alternative
names) and a lambda function (event) called when the option is present/parsed.
There are helper macros `add_bool`, `add_output` for adding bool options and
outputs.

Use `option::description(const std::wstring&)` setter for adding a description
text. The text is used for the generated help.

### option types

There are currently three different types for options
- INT (uses result of std::stoi(arg))
- BOOL (true if arg is one of "", "true", "t", "1", "on", "enabled", "yes"
	false if arg is one of "false", "f", "0", "off", "disbled", "no")
- STRING (any value basically)

### output option

Outputs are not special types. They use STRING type. Output name is also the
name of the option which is used to configure output's target.

Use: `--OUTPUT_NAME @target`.

### default value for an option

Best place to add a default value for an option is in a method `void
options::init_defaults()`.

### negating/disabling options

bool options and output options can be negated by adding `disable-`, `no-` or
`dont-` prefix to the option name. Example:
```
  tml --dont-run --no-dump --disable-debug
```


# Driver

`driver` class manages execution of TML programs.

Before running a TML program we need to create an outputs object which contains
output streams.
Then we have various ways to instantiate a driver object.
We can provide a TML program as a string, as a FILE stream and/or we can also
use options object and specify any option including input programs.
Options object parses arguments and configures streams in the outputs
object.

For execution there are two methods
`step(size_t steps = 1, size_t break_on_step=0, bool break_on_FP = false)` or
`run(size_t steps = 0, size_t break_on_step=0, bool break_on_FP = false)`
0 steps means infinite number of steps and 0 break_on_step means to not break

Example:
```
	outputs oo;
	wstring program = L"a(2). b(?x) :- a(?x).";
	vector<wstring> args{
		L"--dump", "@buffer",
		L"--error", "@buffer" };
	driver d(program, options(&oo, args));
	d.run();
	if (d.result) d.dump();
	else wcout << L"unsat";
	wstring err = oo.read(L"error");
	if (err.size()) wcerr << err;
	wstring dump = oo.read(L"dump");
	if (dump.size()) wcout << dump;
```

To extract result there are several functions:
`driver::dump()` prints database to the "dump" output
`driver::out(wostream&)` prints database to a stream
`driver::out_goals(wostream&)` prints extracted proofs

It is also possible to pass a custom raw term printer:
`driver::out(const tables::rt_printer& p)` which gets called for each printed term.

See actual usage of `driver` in `src/main.cpp` and `src/repl.cpp`


# JS (emscripten) build

There is an emscripten binding allowing TML run in browsers or with Node.js.
Enable the JS build with `-DBUILD_JSLIB=1 -DEMSCRIPTEN_DIR=/path/to/emscripten`

See example usage of JS `driver` in `js/test.html` and `js/tmljs` (Node.js)


# REPL

TML executable can be run in a REPL mode. Enable it with `--repl` option.
REPL mode depends on a TML build configured with `-DWITH_THREADS=TRUE`.

After running `tml --repl` enter `q` to quit, `?` or `h` to print help about
other commands, or enter TML program to evaluate.

REPL can also work over an UDP. Enable it with `--udp` option.
You can specify IP address and port by using `--udp-addr` and `--udp-port`.
Settings default to `127.0.0.1:6283`.
