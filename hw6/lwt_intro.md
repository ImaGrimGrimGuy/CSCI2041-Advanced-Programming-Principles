In this lab we'll be working with the `Lwt` concurrency library; in
order for the code examples to work in `utop`, you'll need to execute
the directive `#require "lwt.simple-top";;` and in order to build
executables using the library you'll need to use the tool `ocamlfind`,
so instead of running `ocamlc -o <myexe> <myprog.ml>`, we'll need to run:
`ocamlfind ocamlc -package lwt -package lwt.unix -linkpkg -o <myexe> <myprog.ml>`
(You'll also need to run against an ocaml installation with `Lwt` installed.
To get this on CSELabs machines, make sure you run `module load soft/ocaml/4.01`.
Otherwise, you can use the `opam` tool to install `Lwt` with the command
`opam install lwt`; you might need to follow some extra steps as directed by
`opam` to get to the point where this command will work.)

`Lwt` is a library for structuring programs to run in concurrent
threads; for more about the abstractions and functions we use in this
lab you can (and should) look at the [online documentation](https://ocsigen.org/lwt/2.5.0/api/Lwt).
The basic ideas behind `Lwt` are:

+ The type `'a Lwt.t`: this represents a thread of execution that when
  completed, will compute a value of type `'a`.  (So `Lwt.t` is a type
  constructor like `list` or `lazy_t`.) Some threads complete
  immediately, others may never complete, and some wait for external
  events or might take time to compute.

+ The `bind` function, which is usually replaced by the infix operator
  `>>=`: if `t1` is a `'a Lwt.t` (thread that will compute a value of
  type `'a`) and `t2` has type `'a -> 'b Lwt.t` (that is, it takes an
  input of type `'a` and results in a thread that will compute a value
  of type `'b`), then `t1 >>= t2` is a `'b Lwt.t`: a thread that will
  compute a value of type `'b` by running `t1` to get a value `v1` and
  then evaluating `t2` with input `v1`.  This might sound confusing,
  but here's an example:

  ```
  open Lwt.Infix
  let t1 = Lwt.return 42
  let t2 = fun a -> Lwt.return (a+21)
  let t3 = t1 >>= t2
  ```

  In this example, `t1 : int Lwt.t` is a thread that when executed, computes the
  integer value `42`; `t2 : int -> int Lwt.t` takes as input a value `a` and
  returns a thread that will compute `a+21`, and `t3 : int Lwt.t` is a thread
  that will compute the integer value `42+21` when run.

+ `Lwt` provides several ways to create threads; we've already seen
  `Lwt.return : 'a -> 'a Lwt.t`, which creates a thread that returns
  its argument.  `Lwt.pause ()` creates a thread which waits for the
  `Lwt` scheduler to run (on which, more below...) and then holds
  `unit`.  `Lwt.wrap f` turns a function `f : unit -> 'a` into a
  thread that will compute `f ()`. `Lwt_list` contains functions that
  turn higher-order list operations into threads. `Lwt_unix.sleep`
  creates a thread that will compute a value of type `unit` in a given
  number of seconds.

+ the `Lwt_io` module provides the type `channel` that represents a
  file or network connection that can be read from or written to.  The
  `Lwt_io.read_line` function creates a thread that will compute a
  string by reading a line of input from a channel, and the
  `Lwt_io.write` and `Lwt_io.print` functions create threads that will
  compute a value of type `unit` by writing to an output channel.

+ The `Lwt_main.run` function wakes up any sleeping threads, and runs a thread
to completion, returning the result computed by the thread. (This function
should *not* be called within a thread; it invokes the "thread scheduler" which
repeatedly determines which threads have computed results, and chooses on of the
threads bound to those threads to execute next, until that thread computes a
result or "yields" to the scheduler by calling `Lwt.yield`, `Lwt.pause`, or some
function that requires external events to complete like i/o or a timer).  The
`Lwt.async` function starts the computation of a thread and does not wait for it
to finish.  To combine threads, the `Lwt.choose` function starts a list of
threads and finishes when one of them completes (whether the others complete or
not), while the `Lwt.join` function starts a list of threads and waits for all
of them to complete. The `Lwt.wait` function returns a pair of threads; the
first waits forever unless it is woken by running the other.

+ By now you might be wondering *How do I get the value a thread has computed?*
Although `Lwt_main.run` returns the result of a thread, this is usually not the
answer: instead, the value computed in one thread is obtained by binding the
thread to the next step, which receives the value as input.  Communication
between threads *can* be achieved using mutable values, which we'll learn about
in a few more lectures, but this can result in unpredictable behavior.
