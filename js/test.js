const Module = require('./tml');

Module['onRuntimeInitialized'] = () => {
	const { tml: tml_js, driver } = Module;
	const tml = tml_js.prototype;
	tml.init();
	const program = "e(1 2). e(?y ?x) :- e(?x ?y).";
	console.log(`running: '${program}'`);
	const d = new driver(0, [], program);
	console.log('result: ', d.result);
};
