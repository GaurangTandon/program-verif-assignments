datatype StateSpace = StateSpace(arr: array<int>, pass: int)

predicate ordered(x: int, y: int) {
	x <= y
}

predicate sorted(arr: array<int>, start: nat, end: nat)
	reads arr
	requires 0 <= start <= end < arr.Length
{
	forall x :: start < x <= end ==> ordered(arr[x - 1], arr[x])
}

method InsertionSortStateTransition(state: StateSpace) returns (finalState: StateSpace)
	modifies state.arr
	requires state.arr.Length >= 1
	requires state.pass == 1
	ensures state.arr.Length == finalState.arr.Length
	ensures sorted(finalState.arr, 0, finalState.arr.Length - 1)
	ensures finalState.pass == finalState.arr.Length
{
	var arr := state.arr;
	var n := arr.Length;
	var i := 1;

	while i < n
		invariant i <= arr.Length;
		invariant sorted(arr, 0, i - 1)
		modifies arr {
			var j := i;

			while j >= 1 && arr[j] < arr[j - 1]
				// ensure that left and right half of
				// the arrays are themselves sorted
				invariant j >= 1 ==> sorted(arr, 0, j - 1)
				invariant j < i ==> sorted(arr, j + 1, i)

				// now that our array is split into three parts
				// values to left of j, value at j, values to right of j
				// establish ordering relations between them
				invariant j < i ==> ordered(arr[j], arr[j + 1])
				invariant 1 <= j < i ==> ordered(arr[j - 1], arr[j + 1])
				modifies arr {
					arr[j], arr[j - 1] := arr[j - 1], arr[j];
					j := j - 1;
			}

			i := i + 1;
	}
	
	finalState := StateSpace(arr, arr.Length);
}

function method rho(arr: array<int>) : StateSpace {
	StateSpace(arr, 1)
}

function method pi(st: StateSpace) : array<int> {
	st.arr
}

method Main(){
	var arr := new int[5];
	arr[0], arr[1], arr[2], arr[3], arr[4] := 2, 1, 3, 4, 5;

	var sts := rho(arr);
	var sts2 := InsertionSortStateTransition(sts);
	var sortedArr := pi(sts2);

	var i := 0;

	while i < sortedArr.Length {
		print sortedArr[i];
		i := i + 1;
	}
	
	assert sorted(sortedArr, 0, sortedArr.Length - 1);
}
