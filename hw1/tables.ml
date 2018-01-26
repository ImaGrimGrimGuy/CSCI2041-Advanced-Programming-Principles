(* tables.ml - CSci 2041 HW 1 table slicer and dicer *)
(* Daniel Hartmann *)
(* Free functions, don't question! *)
(* read std input to eof, return list of lines *)
let read_lines () : string list =
  let rec read_help acc =
    try read_help ((read_line ())::acc) with End_of_file -> List.rev acc
  in read_help []

(* separate a string by delim into a list, trimming surrounding whitespace *)
let make_row delim str =
  let rec trim_strings ls acc = match ls with
  | [] -> List.rev acc
  | h::t -> trim_strings t ((String.trim h)::acc) in
  trim_strings (Str.split (Str.regexp delim) str) []

(* print a list of strings to std output, separated by delim string *)
(* avoids nasty quadratic concatenation behavior *)
let rec write_row r delim = match r with
| [] -> ()
| h::[] -> print_endline h
| h::t -> let () = print_string h in
          let () = print_string delim in write_row t delim

(* Output table using write_row, note let () = ... idiom *)
let rec output_table od t = match t with
| [] -> ()
| r::rs -> let () = write_row r od in output_table od rs

(* Now your turn. *)
(*--------------------------------------universal helper functions----------------------------------*)

(*some primitive operators to ease writing*)
let getcol (_,a,_) = a
let getrow (a,_,_) = a
let getitem (_,_,a) = a

(*more complicated functions*)
 

(*----------------------------------------table_of_stringlist---------------------------------------*)

(*given a string, split it wherever del is encountered and return a list of strings.*)
(*if no instances of del are found, return a one item list containing the string*)
let lists del strl = 
  if (String.contains strl del.[0]) 
  then Str.split(Str.regexp del) strl
  else [strl]

(*iterate through list of strings and make a list of lists, each list on lis countains strings*)
(*separated by delim*)
let rec table_of_stringlist delim rlist = 
  let rec listof accu deli ls = match (accu,deli,ls) with
    |(_, _,[]) ->  List.rev accu
    |(_, dl,hd::tl) -> listof ((lists dl hd)::accu) dl tl 
  in listof [] delim rlist

(*-------------------------------------------make_assoc---------------------------------------------*)

(*given a row, and a row number, will number all columns in the row*)
let rec twos xcor ycor acc l =  match (xcor,ycor,l) with
    |(_,_,[]) -> acc
    |(x,y,hd::tl) -> twos x (y+1) ((x,y,hd)::acc) tl

(*breaks down list of lists into individual lists so that twos (above) can deal with the list*)
let make_assoc rc_list = if (rc_list = []) then [] else
  let rec ones xcoord ycoord accu ls = match (xcoord,ycoord,ls) with
    |(_,_,[]) -> accu
    |(x,y,h::t) -> ones (x+1) y ((twos x y [] h)@accu) t (*pass row coordinate into twos*)
  in ones 1 1 [] rc_list

(*-----------------------------------remap_columns and remap_rows-----------------------------------*)

(*will search a list of tuples given a criteria "term" and where to look for it and put the tuples*)
(*in row/column corresponding to argument "iter"*)
let rec findall typ acc iter term dict = match (term,dict) with
  |(_,[]) -> acc
  |(a,h::t) -> if typ = "col" 
    then( (*check if the column is what you are looking for if so, put on list with new col number*)
      if a = (getcol h) 
        then (findall "col" ((getrow h,iter,getitem h)::acc) iter term t)
        else (findall "col" acc iter term t)
        )
    else( (*same as above comment but replace "column" with row*)
      if a = (getrow h) 
        then (findall "row" ((iter,getcol h,getitem h)::acc) iter term t)
        else (findall "row" acc iter term t)
        )

(* remap the columns of the associative form so that the first column number in clst *)
(* is column 1, the second column 2, ..., and any column not in clst doesn't appear *)
let remap_columns clst alst =
  let rec pickone acc iter cls als = match cls with
  |[] -> List.rev acc
  |h::t -> pickone ((findall "col" [] (iter) h als)@acc) (iter+1) t als
  in pickone [] 1 clst alst

(* remap the rows of the associative form so that the first row number in rlst *)
(* is row 1, the second is row 2, ..., and any row not in rlist doesn't appear *)
let remap_rows rlst alst =
  let rec pickone acc iter cls als = match cls with
  |[] -> List.rev acc
  |h::t -> pickone ((findall "row" [] (iter) h als)@acc) (iter+1) t als
  in pickone [] 1 rlst alst

(*----------------------------------------transpose_table-------------------------------------------*)

(* flip row and column, yeh *)
let transpose_table alist = 
  let rec switch acc lst = match (acc,lst) with
    |(_,[]) -> acc
    |(_,h::t) -> switch ((getcol h,getrow h,getitem h)::acc) t
  in switch [] alist

(*----------------------------------------table_of_assoc--------------------------------------------*)

(* make a list of all items of a specified row in an asscoiative list and return as a table row*)
let rec mkrw row pullist = match pullist with
  |[] -> []
  |h::t -> if (getrow h)=row then (getitem h)::(mkrw row t) else []

(*comapare two lists, remove the items on the first (table) list from the second (associative) list *)
let rec clean dirt cleaned = match (dirt,cleaned) with
  |(_,[]) -> []
  |([],_) -> cleaned
  |(h::t,hd::tl) -> if h=(getitem hd) then (clean t tl) else (clean t cleaned)

(*custom tail recursive function for filtering empty lists from a list of lists*)
let filterblanks lst = 
  let rec safsrch acc ls = match (ls) with
    |[] -> List.rev acc
    |h::t -> if (h = []) then (safsrch acc t) else (safsrch (h::acc) t)
  in safsrch [] lst

(*execute the mkrw and clean functions repeatedly to make an associative list into a table*)
let table_of_assoc alist =  
  let rec choosepath acc rw lst = match (lst) with
    |([]) -> (filterblanks (List.rev acc)) (*reverse and clean up the list*)
    |(_) -> choosepath ((mkrw (rw) lst)::acc) (rw+1) (clean (mkrw (rw) lst) lst)
  in choosepath [] 1 (List.sort compare alist) (*make table row, remove it from the associative list*)
                                                                                   
(*-------------------------------------------test cases---------------------------------------------*)
(*

findall "col" [] 0 1 [(2, 3, "f"); (2, 2, "e"); (2, 1, "d");(1, 3, "c"); (1, 2, "b"); (1, 1, "a")];;
findall "row" [] 0 1 [(2, 3, "f"); (2, 2, "e"); (2, 1, "d");(1, 3, "c"); (1, 2, "b"); (1, 1, "a")];;

let lst1 = [(1,1,"a");(1,2,"b");(1,3,"c");(2,1,"d");(2,2,"e");(2,3,"f");(3,1,"g");(3,2,"h");(3,3,"i")]
let lst2 = []
let lst2 = (mkrw (1) lst1)::lst2)
(mkrw (rw+1) lst1)::acc)
(mkrw (rw+1) lst1)::acc)

remap_columns [1;1;2] [(1,1,"a");(2,1,"b");(1,2,"c");(2,2,"d")] -> [(1,1"a");(2,1,"b");(1,2"a");(2,2,"b");(1,3,"c");(2,3,"d")

(mkrw 1 [(1,1,"a");(1,2,"b");(1,3,"c");(2,1,"d");(2,2,"e");(2,3,"f");(3,1,"g");(3,2,"h");(3,3,"i")])::(mkrw 2 [(2,1,"d");(2,2,"e");(2,3,"f");(3,1,"g");(3,2,"h");(3,3,"i")])

*)

(* OK, more free stuff *)
let main transpose clst rlst id od =
  let sl = read_lines () in
  let rtable = table_of_stringlist id sl in
  let alist = make_assoc rtable in
  let clist = if clst = [] then alist else (remap_columns clst alist) in
  let rlist = if rlst = [] then clist else (remap_rows rlst clist) in
  let tlist = if transpose then transpose_table rlist else rlist in
  let ntable = table_of_assoc tlist in
output_table od ntable
