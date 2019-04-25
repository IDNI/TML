const Module = require('./tml');
Module['onRuntimeInitialized'] = () => {
	const { tml: tml_js, driver } = Module;
	const tml = tml_js.prototype;
	tml.init();
	const program = `
e (v1 v2).
e (v2 v3).
e (v3 v4).
e (v4 v5).
e (v5 v6).
e (v6 v7).
e (v7 v8).
e (v8 v9).
e (v9 v10).
e (v10 v11).
e (v11 v12).
e (v12 v13).
e (v13 v14).
e (v14 v15).
e (v15 v16).
e (v16 v17).
e (v17 v18).
e (v18 v19).
e (v19 v20).
e (v20 v21).
e (v21 v22).
e (v22 v23).
e (v23 v24).
e (v24 v25).
e (v25 v1).
t(?x ?y) :- e(?x ?y).
t(?x ?y) :- t(?x ?z), t(?z ?y).
`;
	console.log(`running: '${program}'`);
	const d = new driver(0, [], program);
	console.log('result: ', d.result);
};
