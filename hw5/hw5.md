# Homework 5: Reasoning about program correctness

*CSci 2041: Advanced Programming Principles, Fall 2017 (afternoon)*

**Due:** Wednesday, November 15 at 11:59pm

our solutions to this homework should be submitted in markdown files
under the directory `hw5` in your personal class repository.  Since
you're submitting them on GitHub, your files can be in
"Github-Flavored Markdown", so if you want to use mathematical
symbols, you can use their
[HTML character entities](http://dev.w3.org/html5/html-author/charref).

Note: the gitbot cannot offer feedback on your solutions to these problems, it will only verify that you have the correct file names and problem headings.

## 1. Induction on integers and `nat`

*Answers to this problem should appear in the file named `hw5/naturals.md`*

In each of the following, you will use natural or structural induction
to prove that a property applies to some infinite set of elements.
For each proof, you should clearly state the property you are proving,
the base case(s) you are proving, the inductive case(s) you are
proving, and what the inductive hypothesis gives you.  Each step in
your proof must be accompanied by a justification explaining why the
step can be taken.

### `power`

Consider the following OCaml function definition:
```
let rec power x n =
  if n = 0 then 1.0
  else x *. (power x n-1)
  ```

Prove that for all `n` &in; &naturals;, for all _x_ &in; `float`:

> `power` _x_ `n` = _x_ <sup>`n`</sup>


### `pow_nat`

Let us adapt `power` to work on elements of the type `nat` defined in
lecture:

```
type nat = Zero | Succ of nat

let rec to_int n = match n with
| Zero -> 0
| Succ n' -> 1 + (to_int n')

let rec pow_nat x n = match n with
| Zero -> 1.0
| Succ n' -> x *. (pow_nat x n')
```

Use structural induction on the type `nat` to prove that for all `n`
&in; `nat`, for all _x_ &in; `float`,

> `power` _x_  (`to_int` `n`) = `pow_nat` _x_ `n`

### `less_nat`

Suppose we want to write code that compares two structured natural
numbers, `m` and `n`:

```
(* test whether m < n without converting to integers *)
let rec less_nat m n = match n with
| Zero -> false (* m is not less than Zero *)
| Succ n' -> if m = n' then true (* n = m+1 > m *)
                 else less_nat m n' (* n > m iff n-1 >= m *)
```

Use structural induction on the type `nat` to prove that for all `m`
&in; `nat`, for all `n` &in; `nat`:

> `less_nat m n` &hArr;  `(to_int m)` < `(to_int n)`.


## 2. Induction on Lists
*Answers to the following questions should appear in a file named `hw5/list.md`*

Use the following function definitions to answer this question:

```
let rec length l = match l with
| [] -> 0
| _::t -> 1 + (length t)

let reverse lst =
  let rec tail_rev lst acc = match lst with
  | [] -> acc
  | h::t -> tail_rev t (h::acc)
  in tail_rev lst []

let tail_sum lst =
  let rec tsum lst acc = match lst with
  | [] -> acc
  | h::t -> tsum t (h+acc)
  in tsum lst 0
```

For each of the following identities, use structural induction on
lists to prove the identity is true for all elements &ell; of type `int
list`.  Your proofs should clearly and formally state property P(&ell;)
to be proved,  the base case, the inductive case, and the inductive
hypothesis.

I. ``length l = length (reverse l)``

II. ``tail_sum l = tail_sum (reverse l)``

## 3. Polynomials
*Answers to this question should appear in a file named `hw5/poly.md`*

Code to manipulate univariate polynomials (e.g. _x_<sup>4</sup> + 3 _x_ + 1, or
(_x_-3)(_x_-7)) turns up in many computer science applications,
including graphics, error-correcting codes, computer algebra, machine
learning and optimization theory.  There are two main methods of
representing polynomials: symbolic and implicit.  The symbolic
representation is essentially another expression type:
```
(* Symbolic representation of univariate polynomials *)
type polyExpr =
| Int of int
| X
| Add of polyExpr * polyExpr
| Mul of polyExpr * polyExpr

(* degree of polynomial p *)
let rec deg p = match p with
| Int _ -> 0
| X -> 1
| Add (e1,e2) -> max (deg e1) (deg e2)
| Mul (e1,e2) -> (deg e1) + (deg e2)

(* Compute a representation of p1(p2(X)) by replacing each instance of
X in p1 with p2 *)
let rec compose p1 p2 = match p1 with
| Int _ -> p1
| X -> p2
| Add (e1, e2) -> Add (compose e1 p2, compose e2 p2)
| Mul (e1, e2) -> Mul (compose e1 p2, compose e2 p2)

(* Some simple arithmetic simplifications on polynomials *)
let rec simplify p =
	let simp_add pp = match pp with
	| (Int 0, p) | (p, Int 0) -> p
	| (Int i1, Int i2) -> Int (i1+i2)
	| (p1,p2) -> Add(p1,p2) in
	let simp_mul pp = match pp with
	| (Int 0, _) | (_, Int 0) -> Int 0
	| (Int 1, p) | (p, Int 1) -> p
	| (Int i1, Int i2) -> Int (i1*i2)
	| (p1, p2) -> Mul(p1,p2) in
	match p with
		| Int _ -> p
		| X -> p
		| Add (p1,p2) -> simp_add (simplify p1, simplify p2)
		| Mul (p1,p2) -> simp_mul (simplify p1, simplify p2)
```

Use structural induction to prove the following identities hold for
all inputs of type `polyExpr`.  As in the previous questions, your proofs should clearly and formally state the property P(_`p`_) to be proved, the base case, the inductive case, and the inductive hypothesis.

I. ``deg (compose p1 p2) = (deg p1)*(deg p2)``

II. ``deg (simplify p) <= deg p``


## All done!

Don't forget to commit all of your changes to the various files required
for this homework, and push them to your individual class repository
on UMN github:

+ `hw5/naturals.md`
+ `hw5/list.md`
+ `hw5/poly.md`

You can always check that your changes have pushed
correctly by visiting the repository page on github.umn.edu.
