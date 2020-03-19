// both start and end are indices in the array
predicate sorted(arr: array<int>, start: int, end: int)
	requires arr.Length > end >= 0
	requires arr.Length > start >= 0
	requires start <= end
	reads arr
{
 forall idx :: start <= idx < end ==> arr[idx] <= arr[idx + 1]
}

predicate isPerm(arr: array<int>, barr: array<int>)
	reads arr, barr
{
	multiset(arr[..]) == multiset(barr[..])
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

	// stops once sortedAbove == 0
	// i.e., all elements are sorted
	while sortedAbove > 0 
		decreases sortedAbove
		invariant 0 <= sortedAbove <= n
		invariant isPerm(arr, old(arr))

		// all elements below sortedAbove must be smaller than those above
		invariant sortedAbove == n || (forall x :: 0 <= x < sortedAbove ==> arr[sortedAbove] >= arr[x])

		invariant sortedAbove >= n || sorted(arr, sortedAbove , n - 1)
	{
		var idx := 0;

		while idx < sortedAbove - 1
			decreases sortedAbove - idx
			invariant 0 <= idx < sortedAbove 
			invariant isPerm(arr, old(arr))
			// the following passes assertion A
 			invariant forall x :: 0 <= x < idx ==> arr[x] <= arr[idx]
		  invariant sortedAbove >= n || sorted(arr, sortedAbove , n - 1)
		{
			if(arr[idx] > arr[idx + 1])
			{
				var temp := arr[idx];
				arr[idx] := arr[idx + 1];
				arr[idx + 1] := temp;
			}

			assert arr[idx] <= arr[idx + 1];
			idx := idx + 1;
		}
		
		assert sortedAbove >= n - 1 || arr[sortedAbove] <= arr[sortedAbove + 1];
		sortedAbove := sortedAbove - 1;
		assert forall x :: 0 <= x < sortedAbove ==> arr[x] <= arr[sortedAbove]; // A
	}
}
