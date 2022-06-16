@string str "2+3/2-(3+2)^2*3".

start =>  start '+' start , 5. 
start =>  start '/' start , 4.
start =>  start '*' start , 4.
start =>  start '-' start , 5.
start =>  '(' start ')', 2.
start =>  start '^' start, 3.
start =>  intn .
start =>  floatn, _pref  .
floatn => intn '.' intn.
floatn => intn.
intn => '2' | '3'.