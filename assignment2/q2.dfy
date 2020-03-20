// using nat datatype since fibonacci is always positive
datatype StateSpace = StateSpace(n: nat, a: nat, b: nat)

function fib(n: nat) : nat
decreases n
{
	if (n == 0) then 0 else if (n == 1) then 1 else fib(n - 1) + fib(n - 2)
}

method FibonacciTransitions(currState: StateSpace) returns (finalState: StateSpace)
	decreases currState.n
	ensures finalState.n == 0
	ensures (currState.a == 0 && currState.b == 1) ==> (finalState.a == fib(currState.n) && finalState.b == fib(currState.n + 1))
{
	var n := currState.n;
	var a := currState.a;
	var b := currState.b;

	if(n == 0){
		finalState := currState;
	}else{
		finalState := FibonacciTransitions(StateSpace(n - 1, b, a + b));
	}
}


function method pi(state: StateSpace): nat
	requires state.n == 0
{
	state.a
}

function method rho(n: nat) : StateSpace
{
	StateSpace(n, 0, 1)
}

method Main(){
	var n := 10;
	var initialState := rho(n);
	var finalState := FibonacciTransitions(initialState);
	var answer := pi(finalState);

	assert answer == 34;
}
