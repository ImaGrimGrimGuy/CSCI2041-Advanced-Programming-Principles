# Homework 4:  Advanced Program Manipulation

*CSci 2041: Advanced Programming Principles, Fall 2017 (afternoon)*

**Due:** Wednesday, November 1 at 11:59pm

## Computing With Program Representations

The `hw4` directory in the public `hw2041-f17a` repo contains several files
related to program parsing and evaluation -- you should copy the entire
directory to your personal repository for use on this homework. The file
`program.ml` contains an implementation of the data structure for representing
simple programs that we covered in Lectures 15-18, along with the type-checking
algorithm and evaluation program.  The file `parser.ml` includes a parser that
transforms prefix-form programs into syntax trees and type-checks these trees.
The file `interpreter.ml` contains code to read a program from standard input,
parse it, type-check it, and evaluate the program.  There are also two very
non-descriptively named example programs, `program1.interp` and
`program2.interp`.  Look over these programs carefully to convince yourself that
you understand how they work, since you'll be modifying them to add new
functionality in this problem.  (Note: to see `interpreter.ml` or one of the
`program1.interp` or `program2.interp` programs in action, you'll need to build
`interpreter` by running `ocamlopt -o interpreter str.cmxa program.ml parse.ml
interpreter.ml` in the `hw4` directory. Note: this will produce a lot of binary files with
suffixes matching `.cm*`; it is best if you do not commit these to your repo, as they
take up a lot of space and thus make pushes and pulls take more time)

### Adding Input Statements

So far, programs in our example can do a lot of interesting things:
for instance, they can run loops, define and call functions, perform
arithmetic and boolean computations, and print out the results of
these computations.  But, there's no way in our language to read an
input from the user.  Let's add a command, `readint` that reads a
single integer into the program.  Programs use this command as if it
were an integer-valued expression, so for example, `(let i readint (print
i))` is a program that reads an integer, binds it to the name `i` and
then prints out `i`. In order to do this, we'll need to:

+ Add a new variant to the `expr` type in `program.ml` for a `Readint`.

+ Add a new constructor `READ` to the `token` type in `parse.ml` for the `readint` keyword.

+ Modify the lexing function, `tokenize_string` to correctly detect and output `READ` tokens

+ Modify `parse_program` to correctly parse the expression `readint`

+ Modify the type checking function, `typeof`, to infer the correct type of a `Readint` value in an expression.

+ Modify the evaluation function to read an integer whenever it
  encounters a `Readint` expression.  You can use the ocaml function
  `read_int ()` to read an integer from the standard input.

Once you've got this all working, you can modify the example program
`program1.interp` so that it reads the values `m` and `n` as input and
then prints the gcd of these values.  (Go ahead and test it out.)

### Constant Folding

A common compiler optimization is to find expressions that contain
only constants and to simplify these expressions before running the
program.  For example, if a loop contains the expression `Add(Const 1,
Mul (Const 2, Mul (Const 3, Const 7)))` the compiler might replace it
with `(Const 43)`, saving one addition and two multiplication
operations every time we execute the loop.  In this problem, we'll
write a function, `const_fold : expr -> expr` that performs this
optimization on a program tree from our language.

Your function should take as input an expression, identify all
subexpressions that consist only of constants and operations on
constants (add, multiply, divide, subtract, and, or, not, comparisons)
and return a new expression that simplifies those expressions to the
constants they represent.  In addition, your program should also
detect and simplify the following situations:

+ `While(Boolean false, body)` should simplify to `Seq []`, an empty
sequence;  (so: `const_fold (While (Boolean false, Const 1))` should evaluate to `Seq []`)

+ `If (Boolean true, thn,els)` should simplify to `thn`; (so `const_fold (If (Boolean true, Const 0, Const 1))` should evaluate to `Const 0`)

+ `If (Boolean false, thn, els)` should simplify to `els`; (so `const_fold (If (Boolean false, Const 0, Const 1))` should evaluate to `Const 1`)

+ Any constant expression before the last one in a `Seq` can be
  removed; An expression of the form `Seq [e]` where `e` is a constant
  expression can be simplified to `e`. So `const_fold (Seq [Const 0; Const 1])` should evaluate to `Const 1`

+ `Let(s,v,b)` can be simplified to `b` if both `b` and `v` can be
  simplified to constants, so for example `const_fold (Let ("x", Const 0, Const 1))` should evaluate to `Const 1`.

Some more complicated evaluations:

+ `const_fold (example3 |> wordlist |> tokens |> parse_program)` should evaluate to

    ```
    Let ("y", Const 0,
     Let ("x", Const 3,
      While (Gt (Name "x", Const 0),
       Seq [Set ("x", Sub (Name "x", Const 1)); Name "x"; Name "y"; While (Boolean true, Print (Name "y")); Boolean true])))
  	```

+ `const_fold (example4 |> wordlist |> tokens |> parse_program)` should evaluate to
    ```
    Let ("y", Const 0,
      Let ("z", If (Gt (Name "y", Const 4), Seq [Set ("y", Sub (Name "y", Const 1)); Const 1], Const 0),
  	  Seq [Print (Name "y"); Let ("z", Readint, Name "z")]))   
    ```

Add your definition of `const_fold` to `parse.ml` and modify
`interpreter.ml` so that it peforms constant folding on `progExpr`,
checks to make sure that the resulting program has the same type as
`progExpr`, and then evaluates the constant-folded program rather than
the original.

### Unused Definition Elimination

Another common compiler optimization is to remove "dead code" - code that does
not have any effect on the outcome of the program, because either it is never run (as in the case of the `If` and `While` optimizations above) or because no other code uses the result of the computation.  In our program representation, one way to arrive at this situation is to have a `Let (n,v,b)` expression in which the body `b` never references the name `n`.  In this case, the `let n=v` is an _unused definition_ and can be eliminated: we can replace `Let (n,v,b)` with simply `b`, removing the need to compute the expression `v`.  For this problem, we'll write a function `unused_def_elim : expr -> expr` that implements this optimization.

Your function should take an expression as input, and recursively identify any subexpressions that contain unused definitions that can be eliminated, resulting in a new expression that does not contain any unused definitions.  This task is complicated by a few exceptional cases:

* Shadow Bindings - if the body of the let expression contains a new binding for
the name `n`, then references to this new name are *not* references to the original
`n`.  For example, `unused_def_elim (Let ("x", Const 1, Let("x", Const 2, Name "x")))` should
evaluate to `Let ("x", Const 2, Name "x")`.  (The other variant that might shadow bind `n` is a `Fun`)

* Side effects - if the value part of the let expression contains side-effects that
change the state of the rest of the program then the definition cannot be eliminated.
So for instance the expression `Let ("x", Set ("y", Const 2), Name "y")` cannot be
simplified - `unused_def_elim (Let ("x", Set ("y", Const 2), Name "y"))` should evaluate to
`Let ("x", Set ("y", Const 2), Name "y")`.  

* Other expression variants that can effect the state of the program include `Print`, `Readint`, and `App` (because the function might execute a side-effecting expression).  So

    + `unused_def_elim (Let ("x",Readint,Const 17))` should evaluate to `Let ("x", Readint, Const 17)`,

    + `unused_def_elim (Let ("x", (Print (Const 1)), Const 0))` should evaluate to `Let ("x", (Print (Const 1)), Const 0)`

    + `unused_def_elim (Let ("x", (Apply (Name "f", Seq [])), Seq []))` should evaluate to `Let ("x", (Apply (Name "f", Seq [])), Seq [])`

* On the other hand, a `Fun` value that is *not* referenced can be eliminated, even if it *would* produce
a side effect if called: so `unused_def_elim (Let ("x",Fun ("s", Unit, Readint),Const 1))` should evaluate to `Const 1`.

One more example evaluation:

+ `unused_def_elim (example5 |> wordlist |> tokens |> parse_program)` should evaluate to

    ```
    Let ("y", Sub (Const 0, Const 0),
     Seq [Print (Name "y"); If (Eq (Add (Const 1, Const 0), Sub (Const 2, Const 1)), Let ("z", Readint, Name "z"), Add (Const 42, Const 17))])               
    ```

Once you've implemented `unused_def_elim`, modify `interpreter.ml` to apply `unused_def_elim` to the input program after constant folding and before evaluation.

### Better Error Messages

Next we'll modify the parser a bit more dramatically: add three new exception variants to `parse.ml`: an `Unclosed` exception for unclosed expressions (or mismatched parentheses), an `Unused` exception for unused tokens in the input, and a `SyntaxError` exception for syntax errors due to unexpected tokens.

The unclosed expression exception should record the position in the token list
where a closing parenthesis was expected; the syntax error and unused token exceptions should record the
position in the token list where they were encountered.

Create a new, position-aware parser, `parse_pos`, which modifies `parse` to keep track of the position in the token list it is processing, and raise the correct exception when the corresponding error is encountered.  In order to handle this, the helper functions in parse_pos will need to be modified to take the position they start *from* as an argument and return the position they parsed *through* as part of the result.

Some examples that should produce exceptions, and the corresponding positions:

+ `parse_pos [OP; OP]` should cause a `SyntaxError` to be raised with argument `1`  (An open paren must be followed by a keyword or close paren; thus the second `OP` token is unexpected)

+ `parse_pos [OP; PLUS; CONST 1; CONST 1; CP; CONST 1]` should cause an `Unused` exception to be raised with argument `5` because the final `CONST 1` token is unused -- the expression `(+ 1 1)` is complete.

+ `parse_pos [OP; TIMES; OP; PLUS; CONST 0; CONST 1; CONST 2; CP; CONST 3; CP]` should cause an `Unclosed` exception to be raised with argument `6` because the `CONST 2` token in position 6 is where a `CP` token was expected to close the `OP` followed by `PLUS` in positions 2 and 3.

Modify `interpreter.ml` to call `parse_pos` in place of `parse` and handle the exceptions
that could be raised in parsing.
## All done!

Don't forget to commit all of your changes to the various files edited
for this homework, and push them to your individual class repository
on UMN github:

+ `program.ml`
+ `parser.ml`
+ `interpreter.ml`
+ `program1.interp`

You can always check that your changes haved pushed
correctly by visiting the repository page on github.umn.edu.
