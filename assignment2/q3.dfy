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

// since `arr` was not declared as array?<int>, it will always have
// non-null type
method bubbleSort(arr: array<int>)
	requires arr.Length >= 1
	modifies arr
	ensures isPerm(arr, old(arr))
	ensures sorted(arr, 0, arr.Length - 1)
{
	var n := arr.Length;
	// bubble sort for n elements array
	// requires n-1 passes

	// index above which all heaviest elements are already collected and sorted
	var sortedAbove := n;

	// stops once sortedAbove == 1
	// i.e., all elements above and including 1 are sorted
	// that implies zero-th element is automatically sorted
	while sortedAbove >= 2
		invariant 0 <= sortedAbove <= n

		invariant isPerm(arr, old(arr))
		invariant sortedAtIndex(arr, sortedAbove)
		invariant sortedAbove < n ==> sorted(arr, sortedAbove, n - 1)
	{
		var idx := 0;
		var farthestIdx := sortedAbove - 2;

		while idx <= farthestIdx
			invariant 0 <= idx <= farthestIdx + 1
			invariant isPerm(arr, old(arr))
		  invariant sortedAbove < n ==> sorted(arr, sortedAbove, n - 1)
			invariant sortedAtIndex(arr, sortedAbove)
 			invariant forall x :: 0 <= x <= idx ==> arr[x] <= arr[idx]
		{
			assert idx <= farthestIdx;

			if(arr[idx] > arr[idx + 1])
			{
				arr[idx], arr[idx + 1] := arr[idx + 1], arr[idx];
			}

			assert arr[idx] <= arr[idx + 1];
			idx := idx + 1;
		}

		sortedAbove := sortedAbove - 1;

		assert sortedAbove < n - 1 ==> arr[sortedAbove] <= arr[sortedAbove + 1];
		assert forall x :: 0 <= x < sortedAbove ==> arr[x] <= arr[sortedAbove];
	}
}
