/**
 * Assuminig  
 * F_1 = 0
 * F_2 = 1
*/

	
// using nat datatype since fibonacci is always positive
datatype StateSpace = StateSpace(n: nat, a: nat, b: nat)

function fib(n: nat) : nat
		requires n >= 1
		decreases n
{
	if (n == 1) then 0 else if (n == 2) then 1 else fib(n - 1) + fib(n - 2)
}

method FibonacciTransitions(initialState: StateSpace) returns (finalState: StateSpace)
	requires initialState.n >= 1
	requires initialState.a == 0
	requires initialState.b == 1
	ensures finalState.n == 1
	ensures finalState.a == fib(initialState.n)
	ensures finalState.b == fib(initialState.n + 1)
{
	var n := initialState.n;
	var a := initialState.a;
	var b := initialState.b;

	var i := 1;
	var nOrg := n + 1;

	while n > 1
		// loop measure
		decreases n
		invariant n >= 1
		// we need to help Dafny get sense of
		// the fact that i == nOrg on loop exit
		// so that it is sure that a == fib(nOrg)
		// on exit
		invariant n + i == nOrg;

		// necessary loop condition
		invariant a == fib(i)
		invariant b == fib(i + 1)
	{
		a, b := b, a + b;
		n := n - 1;
		i := i + 1;
	}

	// just sanity checks
	assert n == 1;
	assert i == nOrg - 1;

	finalState := StateSpace(n, a, b);
}


function method pi(state: StateSpace): nat
	requires state.n == 1
{
	state.a
}

function method rho(n: nat) : StateSpace
{
	StateSpace(n, 0, 1)
}

method Main(){
	assert fib(1) == 0;
	assert fib(2) == 1;

	var n := 10;
	var initialState := rho(n);
	var finalState := FibonacciTransitions(initialState);
	var answer := pi(finalState);

	assert answer == 34;
}
