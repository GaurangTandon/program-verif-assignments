# Assignment 1 on using Sketch

This readme documents my approach to the assignment and my reasoning behind placing different kinds of holes

## Product.sk

In addition to implementing the code with holes, I have also generated several test cases of varying sizes and values using `gen.py` to ensure maximum correctness of my program.

### List of holes placed

1. **Generator** for size of matrix product: suppose we don't know what the size of the product matrix should be, then we can use this generator to generate all possible pairs of dimensions for the matrix size and then Sketch will itself figure out which size should be used.
2. **Constant hole**: placed at `sum = ??`, since we might not know what the initial value of sum should be.
3. **3 Regex holes**: if you do not know what the three limits of the three loops are, you can just replace the limit by `{| M | N | P | Q |}` and let Sketch figure out the answer.

## Linkedlist.sk

I proceeded by:

1. writing a naive implementation of append and insertAt functions
2. writing several tests to ensure append and insertAt work as expected
3. start replacing code with holes, while making sure after every replacement that the generated code looked as expected

### List of holes placed

0. **One generator**: `head = genie(head);` this generates all values satisfying the regex `head(.next)*` and chooses whichever is correct.
1. **1 regex hole**:  `lst.head = {| lst.head | n | n.next |}` when you do not know the value to assign in `insertAt` when pos is 0.
2. **1 regex hole**: `head.next = {| head | n |}` when you do not know what vlaue to assign in the append function after the loop ends.
3. **2 constant holes**: such as `decrease = ??` when you do not know by how the pos variable should decrease at every iteration, and also at `pos == ?` when you do not know the edge case for `insertAt`.
4. **2 regex holes of the form**: `{| n.next | n |}` where in the end of insertAt we do not know how to manipulate pointers and in which direction.