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

method max(arr: array<int>, start: int, end: int) returns (mx: int)
	requires 0 <= start <= end < arr.Length
	ensures forall x :: start <= x <= end ==> arr[x] <= mx
{
	var idx := start + 1;
	mx := arr[start];

	while (idx <= end)
		decreases end - idx
		invariant idx <= end + 1 <= arr.Length
		invariant forall x :: start <= x < idx ==> arr[x] <= mx
	{
		if arr[idx] > mx {
			mx := arr[idx];
		}
		idx := idx + 1;
	}
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
		// and all elmeents above sortedAbove must be sorted themselves
		invariant forall x, y :: (0 <= x < sortedAbove && sortedAbove <= y < arr.Length) ==> arr[x] <= arr[y]
		invariant sortedAbove < n ==> sorted(arr, sortedAbove, n - 1)
	{
		var idx := 0;
		var mx := max(arr, 0, sortedAbove - 1);
		assert mx >= arr[idx];

		while idx < sortedAbove - 1
			decreases sortedAbove - idx
			invariant 0 <= idx < sortedAbove 
			invariant isPerm(arr, old(arr))
			// the following passes assertion A
			invariant arr[idx] <= mx
 			invariant forall x :: 0 <= x < idx ==> arr[x] <= arr[idx]
		  invariant sortedAbove < n ==> sorted(arr, sortedAbove , n - 1)
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

		sortedAbove := sortedAbove - 1;

		assert arr[sortedAbove] == mx;
		assert sortedAbove < n - 1 ==> arr[sortedAbove] <= arr[sortedAbove + 1];
		assert forall x :: 0 <= x < sortedAbove ==> arr[x] <= arr[sortedAbove]; // A
	}
}
