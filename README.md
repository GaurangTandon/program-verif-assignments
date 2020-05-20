These assignments cover the following topics, and you can find more detail in the respective question pdfs:

1. Using Sketch language to write linked list insertion and factorial program
2. Writing fibonacci (iterative, recursive) and Bubble sort in Dafny
3. Writing insertion sort in Dafny.

Sketch programs generate C++ files on their own. They have to be given a basic template of the required program, and it can only have simple "holes", that Sketch will fill in. The holes can be regex based too. You provide several test cases to test the program on, and Sketch will brute force search over the entire valid space of possible holes to generate a correct C++ file.

Dafny is a language with focus on verification using preconditions, postconditions and invariants. Dafny allows the programmer to write methods and specify pre-conditions and postconditions for them. Dafny will keep complaining until the method body guarantees that it does exactly what the postcondition/precondition asked. This is a cool way to write compile-time verifiable programs, that are both syntactically and logically correct.

The preferred choice of editor was Emacs for these assignments, since it has nicer support for these language plugins.
