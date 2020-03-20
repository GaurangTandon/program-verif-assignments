// both start and end are indices in the array
predicate sorted(arr: array<int>, start: int, end: int)
	requires 0 <= start <= end < arr.Length
	reads arr
{
	forall idx :: start <= idx < end ==> arr[idx] <= arr[idx + 1]
}

predicate isPerm(arr: array<int>, barr: array<int>)
	reads arr, barr
{
	multiset(arr[..]) == multiset(barr[..])
}

// all elements below idx must be smaller than those above
// and all elmeents above idx must be sorted themselves
predicate sortedAtIndex(arr: array<int>, idx: int)
	reads arr
{
	forall x, y :: (0 <= x < idx && idx <= y < arr.Length) ==> arr[x] <= arr[y]
}

datatype StateSpace = StateSpace(arr: array<int>, pass: int)

	// since `arr` was not declared as array?<int>, it will always have
	// non-null type
	method BubbleSortStateTransition(state: StateSpace) returns (finalState: StateSpace)
		requires state.arr.Length >= 1
		requires state.pass == state.arr.Length
		ensures isPerm(state.arr, old(state.arr))
		ensures sorted(state.arr, 0, state.arr.Length - 1)
	{
		var n := state.arr.Length;
		var newArr := new int[n];
		var i := 0;
		while i < n {
			newArr[i] := state.arr[i];
		}
		// bubble sort for n elements array
		// requires n-1 passes

		// index above which all heaviest elements are already collected and sorted
		var sortedAbove := state.pass;

		// stops once sortedAbove == 1
		// i.e., all elements above and including 1 are sorted
		// that implies zero-th element is automatically sorted
		while sortedAbove >= 2
		invariant 0 <= sortedAbove <= n
		invariant isPerm(newArr, old(newArr))
		invariant sortedAtIndex(newArr, sortedAbove)
		invariant sortedAbove < n ==> sorted(newArr, sortedAbove, n - 1)
		{
			var idx := 0;
			var farthestIdx := sortedAbove - 2;

			while idx <= farthestIdx
				invariant 0 <= idx <= farthestIdx + 1
				invariant isPerm(newArr, old(newArr))
				invariant sortedAbove < n ==> sorted(newArr, sortedAbove, n - 1)
				invariant sortedAtIndex(newArr, sortedAbove)
				invariant forall x :: 0 <= x <= idx ==> newArr[x] <= newArr[idx]
			{
				if(newArr[idx] > newArr[idx + 1])
				{
					newArr[idx], newArr[idx + 1] := newArr[idx + 1], newArr[idx];
				}

				assert newArr[idx] <= newArr[idx + 1];
				idx := idx + 1;
			}

			sortedAbove := sortedAbove - 1;

			assert sortedAbove < n - 1 ==> newArr[sortedAbove] <= newArr[sortedAbove + 1];
			assert forall x :: 0 <= x < sortedAbove ==> newArr[x] <= newArr[sortedAbove];
		}

		finalState := StateSpace(newArr, 1);
	}

	function method rho(arr: array<int>) : StateSpace {
		StateSpace(arr, arr.Length)
	}

	function method pi(state: StateSpace) : array<int>
		reads state.arr
		requires state.pass == 1
	{
		state.arr
	}

	method Main(){
		var arr := new int[5];
		arr[0], arr[1], arr[2], arr[3], arr[4] := 4, 2, 3, 1, 6;

		var sts := rho(arr);
		var sts2 := BubbleSortStateTransition(sts);
		var sortedArr := pi(sts2);

		assert sorted(sortedArr, 0, sortedArr.Length - 1);
	}
