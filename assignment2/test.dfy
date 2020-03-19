method factorial(n: nat) returns (f: nat){
	f := 1;

		var x := n;
		while (x > 0)
		decreases x
		{
			f := f * x;
			x := x - 1;
		}

		return f;
}

predicate greater(x: int, a: int, b: int){
	(x >= a) && (x >= b)
}

method Max(a: int, b: int) returns (max: int)
	ensures max >= a
	ensures max >= b
	ensures forall x /*{:trigger greater(x,a,b)}*/ :: (greater(x,a,b)) ==> x >= max
{
	if (a > b){
		max := a;
	}else{
		max := b;
	}
//	assert greater(max, a, b);
}

method Abs(x: int) returns (y: int)
	requires x == (-1 / 2)
	ensures y >= 0 && y == -x
{
	y := x + 1;
}

method Main(){
//	var res := Abs(-5);
	//assert res == 5;
}
