# Outputs

`output` is a class wrapping an output stream from TML. It allows to
redirect each of the TML outputs to stdout, stderr, a file, a string
buffer (for reading it later programatically) or to a null.
Outputs are usually configured (targeted) by `options` class.

## printing debugging info

For printing debugging info use a wrapping DBG macro and use `o::dbg()` ostream:
`DBG(o::dbg()<<"debugging output"<<endl);` This works in Debug build.

If you need to print a debugging info in Release build you can use any other
output, for example `o::inf()` ostream (is enabled by `--info` option). See
bellow for the complete list of [default outputs](#default-outputs).

Do not use `std::cout` or `std::wcout`. There is a macro `COUT`, which contains
`std::cout` or `std::wcout` depending on the `WITH_WCHAR` compile option.

It is highly discouraged to commit such printing into a repository because it
cannot be disabled by user and it pollutes the Release build.

If you still need to commit a code which requires to print in Release build
it is adviced to create a dedicated output (disabled by default) and its option
(how to create both is explained bellow).

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
- `o::ms()` - this is output for **benchmarks**
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
	inputs ii;
	outputs oo;
	string program = "a(2). b(?x) :- a(?x).";
	vector<string> args{
		"--dump", "@buffer",
		"--error", "@buffer" };
	driver d(program, options(args, &ii, &oo));
	d.run();
	if (d.unsat) COUT << "unsat";
	else if (d.result) d.dump();
	string err = oo.read("error");
	if (err.size()) COUT << err;
	string dump = oo.read("dump");
	if (dump.size()) COUT << dump;
```

To extract result there are several functions:
`driver::dump()` prints database to the "dump" output
`driver::out(wostream&)` prints database to a stream
`driver::out_goals(wostream&)` prints extracted proofs

It is also possible to pass a custom raw term printer:
`driver::out(const tables::rt_printer& p)` which gets called for each printed term.

See actual usage of `driver` in `src/main.cpp` and `src/repl.cpp`

## Quote

The quote transformation takes a string representing a TML program and the relation name of the domain over which it is defined and stores its syntax tree in relations under the given name. The encoding of the tree into a relation is done as follows: each node in the tree is represented by tuples in several quotation relations. The amount of information stored in each tuple varies depending on the node type, but the following information is always included: a node ID which is a symbol that uniquely identifies the encoded node, and a node type which is a symbol that must come from the set of supported node types. If a given tuple does not represent a leaf node in the syntax tree, then it may contain one or more IDs pointing to the tuples representing the child nodes.

Suppose that a string representing a program written in a simplified subset of TML were quoted into a relation `q`. The following specification shows how `q` might be structured:
```
q_type(<node ID> <node type>).

# <node type> = RULE
q_rule_head(<node ID> <head ID>).
q_rule_body(<node ID> <body ID>).

# <node type> = TERM
q_term_relation(<node ID> <term relation>).
q_term_params(<node ID> <term parameter list>).
q_term_param_types(<node ID> <term param type list>).

# <node type> = AND
q_and_left(<node ID> <left node ID>).
q_and_right(<node ID> <right node ID>).

# <node type> = ALT
q_alt_left(<node ID> <left node ID>).
q_alt_right(<node ID> <right node ID>).

# <node type> = NOT
q_not_body(<node ID> <body node ID>).

# <node type> = FORALL
q_forall_var(<node ID> <variable ID>).
q_forall_body(<node ID> <body node ID>).

# <node type> = EXISTS
q_exists_var(<node ID> <variable ID>).
q_exists_body(<node ID> <body node ID>).

# <node type> = TRUE
```
As can be seen the node type is encoded by the `q_type` relation and the other relations are filled with information specific to the type of node. Note that despite being of fixed arity, quotations can support terms of arbitrary arity by using IDs pointing to lists of parameters and lists of parameter types. The mapping of IDs to specific lists is handled by the domain relation that the quotation is parameterized by. Also note that it might not make sense to put certain node types in certain positions (i.e. a universal quantifier inside a rule head), so TML's grammer must be referred to in order to produce quotation relations that can be understood by other TML constructs like `eval`.

## Eval

The `eval` transformation takes a symbol referring to (defined or undefined) relations containing a quotation, a symbol referring to (defined or undefined) relations containing a domain, and a timeout specifying how many quoted program steps to simulate; and creates an interpreter in the relation of the given name. The interpreter derives the same tuples as would have been derived by the quoted rules it evaluates except that each tuple is now encoded and prepended with a label specifying the name of the deriving quoted rule. That is, if the interpreter is housed in a relation `q` and it is interpreting a quoted rule `r` that would have derived `r(1 2 3)`, then the interpreter derives `q(r <a numerical encoding representing (1 2 3)>)`. The interpreter comprises two parts: one to execute parts of the syntax tree and another to writeback the results into the interpreter relation.

There is an executor for each type of node that can occur in the body of a rule. Its job is to derive a term containing the node ID of the current node if executing it yields `true`. Every executor contains a term to capture the parts of the node type it matches; this might be a term name or conjunct IDs. Every executor also exports all the variables used by the current node and its descendents; this is necessary since any element could potentially be a variable that is referred to somewhere else in the syntax tree. If the node type is simply a term of a given arity, then the executor simply ensures that the interpreter relation has derived a term of the same name and arity. (Note the recursion as the executor is also being referred to by the interpreter rules.) If the node type is a compound like a conjunction, then the executor would instead use the executor relation to execute the child nodes and then use the corresponding host language operator (i.e. `&&`) to combine the results.

Here is an executor for nodes of type `OR`:
```
scratch0(?ts ?id ?out) :-
  quote_type(?id 8), # OR
  quote_or_left(?id ?ql),
  quote_or_right(?id ?qr),
  scratch(?ts ?ql ?out),
  tick().

scratch0(?ts ?id ?out) :-
  quote_type(?id 8), # OR
  quote_or_left(?id ?ql),
  quote_or_right(?id ?qr),
  scratch(?ts ?qr ?out),
  tick().
```
The second and ninth lines are the capturing term described earlier. Note the `?id` term, it represents the ID of the node being interpreted. Note the `8` in the capture term, it ensures that this rule only executes `OR` nodes. Since the result of an `OR` expression is determined by its child nodes, the executor calls itself on the IDs of its child nodes. The variables coming after the IDs in the subcalls are the exported elements that were described earlier; we need these exports in case, for example, the child nodes constrain a common variable. Note that we use two rules to interpret `OR`, this is because we are using the host interpreter's facilities to implement the guest interpreter's facilities.

There is also a writeback for positive and negative rules. Its job is to to call the executor on the rule's body node, select the elements required for the head and label them as described earlier. Every writeback rule contains a term to capture a rule and head nodes, from which it obtains the head name and the body term ID. All writeback rules also contain a term to call the executor on the body and capture the variables computed in the body's execution. And lastly, writeback rules contain terms to correctly fix the head variables to the variables exported from the execution of the body. To interpret a deletion rule, one could negate the head of the writeback rule and make the body only capture head nodes of type `NOT` instead of `TERM`.

Here is an example of a writeback rule for nodes representing arbitrary arity rules:
```
to_add(?ts ?name ?out) :-
  quote_type(?id 1), # RULE
  quote_rule_head(?id ?qh),
  quote_rule_body(?id ?qb),
  quote_type(?qh 2 /*TERM*/),
  quote_term_relation(?qh ?name),
  quote_term_params(?qh ?vars),
  quote_term_param_types(?qh ?chks),
  scratch(?ts ?qb ?vals),
  select(?vars ?chks ?vars_s),
  select(?out ?chks ?out_s),
  gfix(?vals ?vars_s ?out_s),
  deselect(?vars ?chks ?syms),
  deselect(?out ?chks ?syms),
  tick().

databases(?nts ?name ?out) :-
  ?ts + 1 = ?nts,
  in_time(?ts),
  to_add(?ts ?name ?out),
  tock().
```

An interpreter's term arities are limited only by the configuration of the domain that it is parameterized by. Applying an interpreter to a quotation defined on a different domain will in general lead to incorrect results because the executors and the writeback rules will extract incorrect heads and tails from the list IDs.

## Sequencing

The sequencing transformation takes an unsequenced transformation (i.e. a transformation that would be correct if rules instead behaved like macros) and turns it into a sequenced transformation (i.e. a transformation that would be correct if macros instead behaved like rules). The overall idea behind this transformation is to version the relations so that so that the pre-update version has a different name to the post-update version, apply the unsequenced transformation, topologically sort the rules to establish an execution order (of rule sets) that produces the results intended by the unsequenced transformation, and then output these rules with markers indicating relative execution order along with writeback rules to make the post-update relations the new pre-update relations.

It is easiest to understand this transformation through an example. Imagine that we would like to "factorize" the following program:
```
car(?x ?y) :- car(?x ?y), truck(?y ?x).
truck(?x ?y) :- car(?y ?x), truck(?x ?y).
```
Naively replacing 2nd relation with `truck(?x ?y) :- car(?y ?x).` would be incorrect due to staging and mutation of car relation. I.e. even if the `truck` relation obtained the right facts, they would come delayed with respect to the facts in the `car` relation. What we need is for the `car` and `truck` relations to have the correct facts simultaneously. So let us version the relations as follows: `0f10` is car's update and `0f20` is truck's update.
```
0f10(?x ?y) :- car(?x ?y), truck(?y ?x).
0f20(?x ?y) :- car(?y ?x), truck(?x ?y).
```
Now their relative execution order is inconsequential since the rules are independent of each other. The rules can now be treated like macros and be substituted or exapnded freely by any transformation as can be seen in the following:
```
0f10(?x ?y) :- car(?x ?y), truck(?y ?x).
0f20(?x ?y) :- 0f10(?y ?x).
```
Now a topological sort can be used to establish that rule `0f10` should fire before rule `0f20` if their corresponding relations are to contain the updates of `car` and `truck` respectively. After we put in writeback rules to synchronize the original relations with their updates, we should obtain a program that looks as follows:
```
Stage 0:
	0f10(?x ?y) :- car(?x ?y), truck(?y ?x).
Stage 1:
	0f20(?x ?y) :- 0f10(?y ?x).
Stage 2:
	car(?x ?y) :- 0f10(?x ?y).
	truck(?x ?y) :- 0f20(?x ?y).
	~0f10(?x ?y) :- 0f10(?x ?y).
	~0f20(?x ?y) :- 0f20(?x ?y).
```
Note the two deletion rules in stage 2; these are done to prevent the temporary "version" relations from a previous stage from affecting the execution of future stages. The last program above is only pseudo-code, in actuallity the staging would be done by conditioning each of these rules upon the stages of some clock construction.

## Purification

The purification transformation converts TML rules written in first-order logic syntax to (possibly more) rules that are conjunctions of possibly negated negated terms. This is an unsequenced transformation, meaning that the rules that it creates should be treated like macros when reasoning about execution ordering. The transformation works its way up the syntax tree of a first-order logic formula doing the following conversions:

### Conjunction
Handled by creating a new relation whose defining rule has multiple conjuncts.
```
r(...) :- ... { a(?x ?z) && b(?y ?z) } ...
TO
c(?x ?y ?z) :- a(?x ?z), b(?y ?z).
r(...) :- ... c(?x ?y ?z) ...
```

### Disjunction
Handled by creating a new relation whose defining rule has multiple clauses.
```
r(...) :- ... { a(?x ?z) || b(?y ?z) } ...
TO
c(?x ?y ?z) :- a(?x ?z).
c(?x ?y ?z) :- b(?y ?z).
r(...) :- ... c(?x ?y ?z) ...
```

### Negation
Handled by factoring the negation into a separate rule.
```
r(...) :- ... { ~ a(?x ?z) } ...
TO
c(?x ?z) :- ~a(?x ?z).
r(...) :- ... c(?x ?z) ...
```

### Implication
Handled by reduction to negation and disjunction.
```
r(...) :- ... { a(?x ?z) -> b(?y ?z) } ...
TO
r(...) :- ... { { ~ a(?x ?z) } || b(?y ?z) } ...
```

### Coimplication
Handled by reduction to conjunction of implications.
```
r(...) :- ... { a(?x ?z) <-> b(?y ?z) } ...
TO
r(...) :- ... { { a(?x ?z) -> b(?y ?z) } && { b(?y ?z) -> a(?x ?z) } } ...
```

### Existential Quantification
Handled by creating a separate rule in which the quantified variable is free. The solver will find the correct variable assignments if they exist.
```
r(...) :- ... exists ?x { a(?x ?y) } ...
TO
c(?y) :- a(?x ?y).
r(...) :- ... c(?y) ...
```
### Universal Quantification
Handled by reduction to the lack of existence of an object that does not satisfy the given property.
```
r(...) :- ... forall ?x { a(?x ?y) } ...
TO
r(...) :- ... ~ { exists ?x { ~ a(?x ?y) } } ...
```
### Uniqueness Quantification
Handled by reduction to universal and existential quantification and a coimplication.
```
r(...) :- ... unique ?x { a(?x ?y) } ...
TO
r(...) :- ... exists ?u { forall ?x { { ?u = ?x } <-> a(?x ?y) } } ...
```


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
