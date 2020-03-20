// both start and end are indices in the array
predicate sorted(arr: array<int>, start: int, end: int)
	reads arr
	requires 0 <= start <= end < arr.Length
{
	forall idx :: start <= idx < end ==> arr[idx] <= arr[idx + 1]
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
		ensures finalState.pass == 1
		ensures finalState.arr.Length == state.arr.Length
		ensures sorted(finalState.arr, 0, finalState.arr.Length - 1)
	{
		var n := state.arr.Length;
		var newArr := new int[n];
		
		var i := 0;
		while i < n
			invariant i <= newArr.Length
			invariant forall j :: 0 <= j < i ==> newArr[j] == state.arr[j]
		{
			newArr[i] := state.arr[i];
			i := i + 1;
		}
		assert forall i :: 0 <= i < n ==> newArr[i] == state.arr[i];

		// bubble sort for n elements array
		// requires n-1 passes

		// index above which all heaviest elements are already collected and sorted
		var sortedAbove := state.pass;

		// stops once sortedAbove == 1
		// i.e., all elements above and including 1 are sorted
		// that implies zero-th element is automatically sorted
		while sortedAbove >= 2
				invariant 0 <= sortedAbove <= n
				invariant sortedAtIndex(newArr, sortedAbove)
				invariant sortedAbove < n ==> sorted(newArr, sortedAbove, n - 1)
		{
			var idx := 0;
			var farthestIdx := sortedAbove - 2;

			while idx <= farthestIdx
				invariant 0 <= idx <= farthestIdx + 1
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
	{
		state.arr
	}

	method Main(){
		var arr := new int[5];
		arr[0], arr[1], arr[2], arr[3], arr[4] := 4, 2, 3, 1, 6;

		var sts := rho(arr);
		var sts2 := BubbleSortStateTransition(sts);
		var sortedArr := pi(sts2);

		var i := 0;
		while i < sortedArr.Length {
			print sortedArr[i];
			i := i + 1;
		}
		assert sorted(sortedArr, 0, sortedArr.Length - 1);
	}
