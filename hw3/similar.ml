(*Created By Dr Nick Hopper
  Modified by Daniel Hartmann*)
open SimUtil


(*-----------------------------------------------words----------------------------------------------*)
(*cast all uppercase characters to lowercase characters and then replace all characters not a to z 
  with blank spaces, used lowercase instead of lowercase_ascii for compatability with older versions 
  of ocaml*)
let filter_chars s = String.map (fun a -> if (((Char.code (Char.lowercase a)) <= 122) && ((Char.code (Char.lowercase a)) >= 97)) then a else ' ') s

(*Makes a list of strings (words) with no blank spaces and no special characters from a string (paragraph)*)
let words s = List.filter (fun x -> (not (String.contains x ' '))) (split_words (filter_chars s))
(*------------------------------------------------end-----------------------------------------------*)


(*--------------------------------------------wordlists---------------------------------------------*)
(*Map words onto a list of strings to make a list of list of words out of a list of strings*)
let wordlists ls = List.map (fun st -> (words st)) ls
(*------------------------------------------------end-----------------------------------------------*)


(*---------------------------------------------stemlist---------------------------------------------*)
(* Use Stemmer.stem to convert a list of words into a list of stems *)
let stemlist ws = List.map (Stemmer.stem) ws
(*------------------------------------------------end-----------------------------------------------*)


(*----------------------------------------------to_set----------------------------------------------*)
(*get rid of duplicates on a list by checking if an item is already on the new list you are adding it 
to and not adding it if so*)
let to_set lst = List.fold_left (fun acc a -> if List.mem a acc then acc else acc@[a] ) [] lst
(*------------------------------------------------end-----------------------------------------------*)


(*--------------------------------------------similarity--------------------------------------------*)
(* Define the similarity function between two sets: size of intersection / size of union*)

(*check through s1 and see if any of the items of s1 are in s2, add one if this is so*)
let intersection_size s1 s2 = List.fold_left (fun acc a -> if List.mem a s2 then (acc+1) else acc) 0 s1

(*union size a b = size a + size b - size(intersection(a,b)) Inclusion-exclusion principal ;)*)
let union_size s1 s2 = (intersection_size s1 s1) + (intersection_size s2 s2) - (intersection_size s1 s2)

(*cast to floats and divide!*)
let similarity s1 s2 = (float_of_int (intersection_size s1 s2))/.(float_of_int (union_size s1 s2))
(*------------------------------------------------end-----------------------------------------------*)


(*---------------------------------------------find_max---------------------------------------------*)
(* Find the most similar representative file by swapping greater tuples in for the one you're on over 
and over again call max repeatedly to accomplish the swapping*)
let find_max repsims repnames = List.fold_left (fun acc a -> max acc a) (0.0,"") (List.combine repsims repnames)
(*------------------------------------------------end-----------------------------------------------*)


(*------------------------------------------------main----------------------------------------------*)
let main all replist_name target_name =
  (* Read the list of representative text files with file_lines*)
  let repfile_list = file_lines replist_name in
  (* Get the contents of the repfiles and the target file as strings by mapping string versions of 
     the files onto each of their respective file names*)
  let rep_contents = List.map (file_as_string) (repfile_list) in
  let target_contents = file_as_string target_name in
  (* Compute the list of words from each representative *)
  let rep_words = wordlists rep_contents in
  (* Convert the target text file into a list of words *)
  let target_words = words target_contents in
  (* Compute the lists of stems in all rep files and the target file *)
  let rep_stemlists = List.map (stemlist) rep_words in
  let target_stemlist = stemlist target_words in
  (* Convert all of the stem lists into stem sets *)
  let rep_stemsets = List.map to_set rep_stemlists in
  let target_stemset = to_set target_stemlist in
  (* Compute the similarities of each rep set with the target set *)
  let repsims = List.map (similarity target_stemset) rep_stemsets in
  
  let (sim,best_rep) = find_max repsims repfile_list in
  
  let () = if all then
  (* print out similarities to all representative files if user requests it with all *)
  let () = print_endline ("File\tSimilarity")in
  (*use List.iter2 and print_endline to iterate through and print a list of tuples, separated by a 
    tab. cast similarity from float to string*)
  (List.iter2 (fun a b -> print_endline ((a)^"\t"^(string_of_float b))) repfile_list repsims) else begin 
  (* Print out the winner and similarity *)
  let () = print_endline ("The most similar file to "^target_name^" is "^best_rep) in
  print_endline ("Similarity: "^(string_of_float sim)) end in
  (* this last line just makes sure the output prints before the program exits *)
  flush stdout
(*------------------------------------------------end-----------------------------------------------*)
