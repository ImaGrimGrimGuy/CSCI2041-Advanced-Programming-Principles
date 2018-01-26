# Homework 1: Table Slicing and Dicing

*CSci 2041: Advanced Programming Principles, Fall 2017 (afternoon section)*

**Due:** Wednesday, September 20 at 11:59pm

In the `hw2041-f17a/hw1` directory, you will find a files named `tables.ml` and `slicendice.ml`.
Create a directory named `hw1` in your personal repository, and copy both of these files
to your `hw1` directory.  Don't forget to run `git add` on both the directory and
the files!

## Background: Command Line programs

Every (but one) homework in this class will involve eventually creating a
program that can be run from the "command line" in a terminal.  We will
typically include directions for building these programs in the homework.  They
can usually be compiled with `ocamlc` or `ocamlopt` but sometimes (later in the
semester) we'll use additional libraries and it will be easier to use
`ocamlbuild` to resolve the dependencies between files.  

Command line programs typically take arguments on the command line, for example,
like `git` or `ssh`.  They also often need to read or write outputs to files, or
in the case of many *nix utilities, can read an input file from the "standard
input" and write to the "standard output."  As you probably know, a command line
program's standard input can be "redirected" to use a file with the `<`
operator, and its standard output can be redirected with the `>` operator.  (So
for example, if you type `git status >git.out` in the terminal while your
working directory is within a git repo, the result will go to a file named
`git.out` that you can read with your favorite text editor, or `less`)

## Background: Tables

A very common way of storing data for presentation or manipulation is as a table.  While spreadsheet applications like Excel, Numbers, Google Sheets, and LibreOffice each have their own customized format for storing tables, it is also common to store tables as lines of a text file, with a "delimiter" character between the columns in each row.  So the table:

Last Name | First Name | Birth Year | Email | House
--- | --- | --- | --- | ---
Potter  | Harry | 1980  | pott213@hogwarts.ac.uk | Gryffindor
Granger | Hermione | 1979 | gran371@hogwarts.ac.uk | Gryffindor
Malfoy | Draco | 1980 | malf091@hogwarts.ac.uk | Slytherin
Chang | Cho | 1979 | chan010@hogwarts.ac.uk | Ravenclaw
Diggory | Cedric | 1977 | digg131@hogwarts.ac.uk | Hufflepuff

Might be stored in a file named `students.csv` with contents:

```
Last Name, First Name, Birth Year, Email, House
Potter, Harry, 1980, pott213@hogwarts.ac.uk, Gryffindor
Granger, Hermione, 1979, gran371@hogwarts.ac.uk, Gryffindor
Malfoy, Draco, 1980, malf091@hogwarts.ac.uk, Slytherin
Chang, Cho, 1979, chan010@hogwarts.ac.uk, Ravenclaw
Diggory, Cedric, 1977, digg131@hogwarts.ac.uk, Hufflepuff
```

Here the delimiter is `,`; if you are reading this file in a text editor, you'll
notice that markdown also stores tables as a collection of lines, with columns
delimited by `|`.  Another common delimiter for storing tables in text files is
the tab character, `\t`.

This table has six *rows*, including the headings, and five *columns*.
Sometimes it might be useful to look at only a *subset* of the columns, or only
*some* of the rows, or have the columns rearranged; or we might want to
*transpose* a table so that rows become columns, and vice versa.  For Homework
1, we'll write a tool that supports these operations, and translates between
different delimiter formats as well.

## Homework 1: `slicendice`

Open `tables.ml` in your favorite text editor, and you'll see that there's some
implementation in the file already:

+ `read_lines : unit -> string list` reads from standard input and returns a
list of strings, one for each line in the input.

+ `make_row : string -> string -> string list` takes a delimiter and a line, and
returns a list of strings separated by the delimiter.  It trims extra whitespace
from these strings as well.

+ `write_row : string list -> string -> unit` takes a list of strings `r` and a
delimiter `delim`, and writes each string in `r` to the standard output, with
the string `delim` as the delimiter.

+ `output_table : string -> string list list -> unit` takes a delimiter and a
list of lists of strings, and prints each string list as a separate line
(delimited by the first input) on the standard output.

There's one more function fully implemented in `tables.ml`, which is `main`.  This function handles the flow of work to be done by our tool:

+ Read the input from stdin, storing it as a list of strings.

+ Then convert the list of strings into "table format," a list of lists of strings.  The function `table_of_stringlist`, which you'll fill in, does this.

+ Next, convert from this table format to a more convenient representation for the job we want to do, *associative format*.  When we're manipulating a table, we'll store it as a `int*int*string list`, that is a single list of triples, where if the triple `(r,c,e)` is in the list, this means that the string `e` is in the table at row `r` and column `c`.  This is accomplished by the function `make_assoc`.

+ Next, select and re-order the columns as indicated on the command line; if the user runs the command with argument `--cols 4,3` then the 4th column (starting from 1) of the input should be the first column in the output, and the 3rd column of the input should be the 2nd column of the output, and the remaining columns should be dropped.  (So in the table above, the first row of output would be `Email,Birth Year`).  This is handled by the function `remap_columns`.

+ Next, select and re-order rows, using the same convention as described above for columns, accomplished in `remap_rows`.

+ Next, if the user has asked us to transpose the table, do so; the function `transpose_table` handles this transformation.  (In the transposed table, if an element was at row `r` and column `c` originally, it will appear at row `c` and column `r` in the output.)

+ Finally, convert the associative representation back into a table representation, e.g. a `string list list`, in `table_of_assoc`, and pass the result to `output_table`.

A separate file, `slicendice.ml` contains code to read the command-line arguments and call the `main` function in `tables.ml`:

+ `parse_rc_list` separates a command-line string listing column or row indices (like `"4,3"`) into a list of integers, like `[4; 3]`.

+ `slice_and_dice` handles the job of understanding the command-line arguments
to our tool, and

+ evaluating the line below it, `let () = ...` is what causes all of the functions to be called with appropriate arguments.

The files as given will compile (with `ocamlc -o slicendice str.cma tables.ml slicendice.ml`) but the resulting program won't produce useful output until you fill in all of the incomplete functions:

### 1. `table_of_stringlist`

The function `table_of_stringlist : string -> string list -> string list list` takes as input a list of strings, and converts each string in the list into a list of strings using `make_row` with the first parameter as a delimiter.  So `table_of_stringlist d [r1;r2;...;rN]` should evaluate to `[(make_row d r1); (make_row d r2); ...; (make_row d rN)]`.  Some example evaluations:

+ `table_of_stringlist "," ["a"]` should evaluate to `[["a"]]`

+ `table_of_stringlist "," ["a,b"]` should evaluate to `[["a"; "b"]]`

+ `table_of_stringlist "|" ["a|b|c"; "d"]` should evaluate to `[["a";"b";"c"]; ["d"]]`.

### 2. `make_assoc`

The function `make_assoc : string list list -> (int*int*string) list` should translate a list of lists of strings into *associative form*: the list `[[s11;...;s1k]; [s21;...;s2m];...[sN1;....;sNl]]` should be translated to `[(1,1,s11);...;(1,k,s1k);(2,1,s21);...;(2,m,s2m);...;(N,1,sN1)...;(N,l,sNl)]`. Some concrete evaluations:

+ `make_assoc []` and `make_assoc [[]]` should both evaluate to `[]`

+ `make_assoc [["a"]]` should evaluate to `[(1,1,"a")]`

+ `make_assoc [["a";"b"];["c"]]` should evaluate to (a permutation of) `[(2,1,"c"); (1,2,"b"); (1,1,"a")]`

### 3. `remap_columns` and `remap_rows`

The function `remap_columns : int list -> int*int*string list -> int*int*string list` takes a list of column indexes and a table in associative form.  For each column index in the first list, any entry matching this column should be mapped to a new entry with a column equal to its position in the first list.  For example, `remap_columns [3] [(1,3,"a")]` should evaluate to `[(1,1,"a")]`, because the column in `(1,5,"a")` matches `5`, which is in position `1` in the first list. Entries in the associative table with columns that do not appear in the index list should not appear in the result, so `remap_columns [1] [(1,2,"a")]` should evaluate to `[]`.  Repeated columns in the index list should result in multiple entries in the output, so `remap_columns [1;1] [(1,1,"a")]` should evaluate to `[(1,1,"a"); (1,2,"a")]` (or some permutation of this list).

`remap_rows` has the same behavior, but applied to the row of each entry, rather than the column.

### 4. `transpose_table`

The function `transpose_table : ('a*'b*'c) list -> ('b*'a*'c) list` takes a table in associative form and returns the table with the rows and columns transposed, e.g. if `(r,c,e)` is in the input list, then `(c,r,e)` should be in the output list.  `transpose_table` may output the list in a different order than the input list.  Some example evaluations:

+ `transpose_table [(1,1,"a"); (1,2,"b"); (1,3,"c"); (2,1,"d"); (2,2,"e"); (2,3,"f")]` should evaluate to (a permutation of) `[(1,1,"a"); (2,1,"b"); (3,1,"c"); (1,2,"d"); (2,2,"e"); (3,2,"f")]`.

+ `transpose_table [(1,4,"h")]` should evaluate to `[(4,1,"h")]`

+ `transpose_table []` should evaluate to `[]`

### 5. `table_of_assoc`

The function `table_of_assoc : (int*int*'a) list -> 'a list list` takes as input a table in associative form and returns the table as a list of lists of strings, where the first string list represents the first row, the second represents the second row, and so on.  So `table_of_assoc [(1,1,"a")]` should evaluate to `[["a"]]`, `table_of_assoc [(1,1,"a"),(2,1,"b")]` should evaluate to `[["a"]; ["b"]]`, and `table_of_assoc [(1,1,"a"),(1,2,"b")]` should evaluate to `[["a"; "b"]]`.  Your solution may make some assumptions about the associative form:

+ If a column index `c` occurs in some `(r,c,e)` entry, then it is present for every row index that also occurs in the input.  Thus your solution doesn't need to consider inputs like `[(1,1,"a"); (1,2,"b"); (2,1,"c")]`.  Similarly, if a row index occurs in some entry, it is present for every column index that also occurs in the input.  

+ Any missing row or column indices should be skipped, so `table_of_assoc [(1,1,"a"); (1,3,"b"); (3,1,"c"); (3,3,"d")]` should evaluate to `[["a"; "b"]; ["c"; "d"]]`.  

+ No duplicate row, column pairs occur in the input.  So your solution doesn't need to consider inputs like `[(1,1,"a"); (1,1,"b")]`.

You might find it useful to be able to sort lists for this function: in that case, the function `List.sort : ('a -> 'a -> int) -> 'a list -> 'a list` will be useful.  The first argument to this function is a "comparison" function that should return 0 if its arguments are equal, a positive value if the first argument is greater than the second, and a negative value otherwise.

## Other considerations

In addition to satisfying the functional specifications given above, your code should be readable, with comments that explain what you're trying to accomplish.  It must compile with `ocamlc -c str.cma tables.ml`.  It must be committed in the `hw1` directory of your personal repository.  Finally, solutions that pay careful attention to resources like running time and stack space (e.g. using tail recursion wherever feasible) and code reuse are worth more than solutions that do not have these properties.
