// using nat datatype since fibonacci is always positive
datatype StateSpace = StateSpace(n: nat, i: nat, a: nat, b: nat)

function fib(n: nat) : nat
	requires n >= 1
decreases n
{
	if (n == 1) then 0 else if (n == 2) then 1 else fib(n - 1) + fib(n - 2)
}

method FibonacciTransitions(currState: StateSpace) returns (finalState: StateSpace)
	decreases currState.n - currState.i
	requires 1 <= currState.i <= currState.n
	requires currState.a == fib(currState.i)
	requires currState.b == fib(currState.i + 1)
	ensures finalState.n == finalState.i
	ensures finalState.a == fib(currState.n)
	ensures finalState.b == fib(currState.n + 1)
{
	var n, i, a, b := currState.n, currState.i, currState.a, currState.b;

	if(i == n) {
		finalState := currState;
	} else {
		var nextState := StateSpace(n, i + 1, b, a + b);
		finalState := FibonacciTransitions(nextState);
	}
}

function method pi(state: StateSpace): nat
{
	state.a
}

function method rho(n: nat) : StateSpace
	requires n >= 1
{
	StateSpace(n, 1, 0, 1)
}

method Main(){
	var n := 10;
	var initialState := rho(n);
	var finalState := FibonacciTransitions(initialState);
	var answer := pi(finalState);

	assert answer == 34;
}
