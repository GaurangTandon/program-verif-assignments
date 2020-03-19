// using nat datatype since fibonacci is always positive
datatype StateSpace = StateSpace(n: nat, a: nat, b: nat)

function fib(n: nat) : nat
decreases n
{
	if (n == 0) then 0 else if (n == 1) then 1 else fib(n - 1) + fib(n - 2)
}

method FibonacciTransitions(initialState: StateSpace) returns (finalState: StateSpace)
	requires initialState.n >= 0
	requires initialState.a == 0
	requires initialState.b == 1
	ensures finalState.n == 0
	ensures finalState.a == fib(initialState.n)
	ensures finalState.b == fib(initialState.n + 1)
{
	var n := initialState.n;
	var a := initialState.a;
	var b := initialState.b;

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
