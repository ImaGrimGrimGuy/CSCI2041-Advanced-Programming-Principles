# Homework 3:  Mapping, Folding and Filtering away recursion
*CSci 2041: Advanced Programming Principles, Fall 2017 (afternoon)*

**Due:** Wednesday, October 18 at 11:59pm


## Overview: Document Similarity without recursion

In this problem, we will write an entire command-line application that
computes an iterative task without any explicit recursion or looping.

The problem our application will solve is based on the idea of
*document similarity*, which is a first step in many "big data"
applications such as improving search, automated document
classification, automated document summary, authorship attribution,
and plagiarism detection.  In this task, we are given a (text) document `d`
to classify along with a list of "representative" documents
`[r_1; r_2; ...; r_N]`, and must choose the document `r_i` that is most
"similar" to `d`.   Your program will be run from the command line
with two arguments - the name of a file listing the files holding the
representative documents, and the name of a target file.  Eventually,
your program will compare this target file to each file listed in the
first file, decide which is the most similar, and print out a message
reporting the most similar document and how close it is to the target
document.

The beginnings of this application, as well as some examples you can
use to test it, are stored in the public `hw2041-f17a` repository under
the `hw3` directory.  You should copy this directory to your personal repository
and work there.  A note about testing your code, which will go in the file `similar.ml`, for this problem: the code in `simUtil.ml` uses the `Str` module, and you'll need to use some `SimUtil` functions for your work.  You'll also need to use a function defined in the file `stemmer.ml`.  So before you start testing functions in `UTop`, you'll need to issue the following directives:

```
utop # #load "str.cma";;
utop # #mod_use "simUtil.ml";;
utop # #mod_use "stemmer.ml";;
```

(`#mod_use "file.ml"` is like `#use "file.ml"` except that the functions and values declared in `file` can be accessed as a module, e.g. as `File.func`)

Follow along as we build our application:

### Reading the file list

Your program should read the list of names of representative files from a file
whose name is passed in as the first command line argument.  For
instance, if we call your program from the command line as
`findsim replist.txt example.txt` then the file `replist.txt`
should contain a list of representative text files, one on each line.
The file `simUtil.ml` contains definitions for the two I/O functions
you'll need for this assignment; `file_lines : string -> string list`
takes as input a file name and returns a list of lines in the file.

Modify the first line of `main` -- `let repfile_list = [""]` -- to bind `repfile_list` to the list of file names stored in the file named by the argument `replist_name`.


### Reading the representative files, and the document

The other I/O function defined in `simUtil.ml` is `file_as_string :
string -> string`: given a file name, it returns the entire
contents of the file as a string.  Still working in the `main` function at the bottom of `similar.ml`, modify the next two lines so that using `file_as_string` and an appropriate list function, `target_contents` is bound to the contents of the target file (passed as a name in `target_name`), and `rep_contents` is bound to a list of strings, containing the string contents of each representative file.

### Splitting into words

Our distance mechanism treats text documents as sets of words.  In
anticipation of this, we'll want to "split" the contents of each text file
into a list of words.  The function `split_words : string -> string list`
defined in `simUtil.ml` will accomplish this goal, but it has some
pecularities:

1.  First, the function doesn't handle punctuation, digits
	and other non-alphabetic characters well.  We can handle this by
	"preprocessing" the string using `String.map` to turn any
	non-alphabetic character into a space, `' '`.  Fill in the function `filter_chars` to accomplish this goal.  Some example evaluations: `filter_chars "abc123"` should evaluate to `"abc   "` and `filter_chars "SAD!!!!!!!"` should evaluate to `"SAD       "`.

2. Second, the `string list` returned will include some strings that
   are just sequences of space characters.  We can remove these from the
   result of `split_words` using a `List` higher-order function;
   `String.contains s c` will tell us if string `s` contains character
   `c`.  

Define a function, `words : string -> string list` that combines the
preprocessing in step 1 with a call to `split_words` and the
postprocessing (removing whitespace strings) in step 2 into a single
function. Some examples: `words "I am *not* 42 letters long"` should
evaluate to `["I"; "am"; "not"; "letters"; "long"]` and `words
"one_word"` should evaluate to `["one"; "word"]`.  Remember, use `let`
and `List` and `String` functions only (plus `split_words`), no
recursion!

Once you've got `words` working, modify the next two let bindings in main so that:

+ `rep_words` is bound to a list of lists of words, one list for each representative text file
+ `target_words` is bound to a list of the words in the target text file

### Canonicalization

There can be many forms of the same word in a document, for example
`Run`, `RUN`, and `run` are all the same word, and `runs`, and
`running` are also forms of the same word.  The process of converting
different forms of a value to the same internal representative is
called *cannonicalization* and in text processing is also called
*stemming*.  The file `stemmer.ml` contains code to stem a word: you
can access the stemming function as `Stemmer.stem : string -> string`.
(Two notes: First, don't worry about trying to understand what this
module does; think of it as a black box.  Second, if you want to be
able to access this function in `utop`, you need to `#mod_use
"stemmer.ml";;` to read and compile it as a module for use in the
toplevel shell.)

Fill in the definition of the function `stemlist : string list -> string list` that converts a list of words to a list of stems.  For example,  `stemlist ["happiness"; "is"; "happy"]` should evaluate to `["happi"; "is"; "happi"]`.

Now modify the next two let bindings in `main` to stem all of the words created
in the previous step: `rep_stemlists` should be bound to a `string list list`,
where each `string list` is the list of stems in the corresponding
representative file, and `target_stemlist` is the list of stems in the target file.

### Converting to sets

Since we're actually representing each text document by the _set_ of
stems it contains, rather than the _list_ of stems (so, no
duplication!), we need a function to convert lists into sets.  Add a
function definition (using `let`, not `let rec`) for the function
`to_set : 'a list -> 'a list` using an appropriate `List` higher-order
function (you may find it useful to also use `List.mem` somewhere in
your definition).  Some examples: `to_set ["a"; "b"; "a" ; "b"]` should
evaluate to (a permutation of) `["a"; "b"]` and `to_set ["a"; "a"; "b"; "c"; "b"; "a"]` should evaluate to (a permutation of) `["a"; "b"; "c"]`.

Modify the next two let bindings to convert the list of lists of stems (`rep_stemlists`) into a list of sets of stems (`rep_stemsets`) from the representative documents, and convert the list of stems from the target document (`target_stemlist`) into a set of stems (`target_stemset`).

### Define the similarity function

We define the similarity between two documents to be the ratio of the
size of the intersection of their stem sets to the size of the union
of their stem sets.  Add function definitions that use `List`
functions to compute the `intersection_size : 'a list -> 'a list ->
int`, the intersection size of two sets represented by lists (you may
assume the inputs are proper sets with no repeated elements);
`union_size : 'a list -> 'a list -> int`, the size of the union of two
sets represented by lists; and `similarity : 'a list -> 'a list ->
float`.  (Don't forget to convert to floats before the division!)
Some examples: `intersection_size ["a"; "b"] ["a"]` should evaluate to
`1`, `union_size ["a"; "b"] ["a"]` should evaluate to `2` and
`similarity ["a"; "b"] ["a"]` should evaluate to `0.5`.

Modify the next let binding to compute `repsims`, the list of similarities between each representative document and the target file.

### Compute the closest document

Now that we have stem sets for all of the representative files and the target
file, and the similarities of each representative file to the target file, we
can compute which representative file is most simliar to the target text file,
and its similarity to the target file.  Fill in the definition of the function
`find_max : float list -> string list -> float*string` which finds the name and
similarity of the file closest to the target document.  If two or more representative
files have the same similarity, your function should return the file name that is
lexicographically greatest, and if the input lists are empty, it should return `(0.,"")`.
A few hints:

+ The list function `List.combine` is the same as the `zip` function
we have seen in class before

+ The built-in function `max` on tuples orders its arguments by the first element of the tuples, then the second, and so on.

An example evaluation: `find_max [0.;0.2;0.1] ["a";"b";"c"]` should evaluate to `(0.2,"b")`.  Once you've defined `find_max`, modify the next `let` binding in `main`
so that `best_rep` is the name of the most similar representative file and `sim` is its
similarity to the target file.

### Print out the result(s)

Finally, now that you have the result, modify `main` so that:

- if the "all" parameter is true, we print out a header line in the format `"File\tSimilarity"`, and then the similarity and file name of each representative
file to the target file are printed, in the order they appear in the repfile_list,
one per line, in the format `"<repfile name>\t<score>"`.  You may find the function `List.iter2` helpful for this case.

- Otherwise, print out two lines telling us the best result.  On the first line,
you should print `"The most similar file to <target file name> was <representative file name>"`, and on the second line, print `"Similarity: <score>"`.

Testing it out: compiling the entire application requires a specific sequence of
arguments to `ocamlc`, because the OCaml compiler does not resolve
"dependencies" automatically - it can't figure out which source files reference other
source files or libraries, requiring those to be built or linked first.  So we'll need
to list them in the right order.  Here's what we know:

+ The source file `findsim.ml` is the command-line driver that calls `main` in
`similar.ml` with the command-line arguments.  So it needs to be compiled after
`similar.ml`

+ `similar.ml` should call functions in `simUtil.ml` and `stemmer.ml`, so it needs
to be compiled after both of those files.

+ `stemmer.ml` and `simUtil.ml` both call the `Str` module, but don't have any dependencies between them.  So the first thing we need to tell `ocamlc` to include is `str.cma`, and these two could come in either order.

Putting these all together, we can compile our application with the command:

```
% ocamlc -o findsim str.cma simUtil.ml stemmer.ml similar.ml findsim.ml
```

Once we've built the executable file, we can test it out.  The directory
`corpus` contains a set of 10 text files taken from the beginnings of 10 random
wikipedia articles.  The files `rlist1` and `rlist2` contain different subsets
of the corpus.  If we run `findsim` with these representative lists against
various target files not on the list, we should see the following output:

```
(repo-user1234/hw3/ ) % ./findsim rlist2 corpus/archivproduktion.txt
The most similar file to corpus/archivproduktion.txt was ./corpus/liltroy.txt
Similarity: 0.102803738318
(repo-user1234/hw3/ ) % ./findsim --all rlist2 corpus/christinecaughey.txt
File	Similarity
./corpus/amirsuri.txt	0.0724637681159
./corpus/beatrizenriquezdearana.txt	0.0809248554913
./corpus/charlesfrench.txt	0.0806451612903
./corpus/liltroy.txt	0.0804020100503
./corpus/mrmusic.txt	0.0801886792453
./corpus/xfiles.txt	0.0714285714286
(repo-user1234/hw3/ ) % ./findsim rlist1 corpus/charlesfrench.txt
The most similar file to corpus/charlesfrench.txt was ./corpus/archivproduktion.txt
Similarity: 0.0915492957746
(repo-user1234/hw3/ ) % ./findsim --all rlist1 corpus/liltroy.txt
File	Similarity
./corpus/amirsuri.txt	0.10152284264
./corpus/archivproduktion.txt	0.102803738318
./corpus/beatrizenriquezdearana.txt	0.0756302521008
./corpus/christinecaughey.txt	0.0804020100503
./corpus/floridasmallbusinessdevelopmentcenternetwork.txt	0.103448275862
./corpus/mrmusic.txt	0.103703703704
./corpus/thetis.txt	0.0863636363636
./corpus/xfiles.txt	0.103571428571
```

## All done!

In addition to satisfying the functional specifications given above, your code should be readable, with comments that explain what you're trying to accomplish.  It must compile with the command line given above.  It must be committed in the `hw3` directory of your personal repository. It must not use any recursive `let`s in the `similar.ml` file.  Finally, solutions that pay careful attention to resources like running time and stack space (e.g. using tail recursion wherever feasible) and code reuse are worth more than solutions that do not have these properties.  When you're done, make sure you commit and push all of your work to `github.umn.edu`.
