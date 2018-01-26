(*------------------------------------------stuff we were given-------------------------------------*)
(* read std input to eof, return list of lines *)
let read_lines () : string list =
  let rec read_help acc =
    try read_help ((read_line ())::acc) with End_of_file -> List.rev acc
  in read_help []

(* split a string at word boundaries and parens *)
let wordlist s : string list =
  let splitlist = Str.full_split (Str.regexp "\\b\\|(\\|)") s in
  let rec filter_splist lst = match lst with
    | [] -> []
    | (Str.Delim "(")::t -> "(" :: (filter_splist t)
    | (Str.Delim ")")::t -> ")" :: (filter_splist t)
    | (Str.Delim _) :: t -> filter_splist t
    | (Str.Text s) :: t -> let s' = String.trim s in
			   let t' = (filter_splist t) in
			   if not (s' = "") then s' :: t' else t'
  in filter_splist splitlist

(* is s a legal variable name? *)
let is_varname s =
  let rec checker i =
    if i = 0 then
      'a' <= s.[i] && s.[i] <= 'z'
    else
      (('a' <= s.[i] && s.[i] <= 'z') ||
  	   ('0' <= s.[i] && s.[i] <= '9')) && checker (i-1)
  in checker ((String.length s) - 1)

(*tokens :)*)
type bexp_token = OP | CP | NAND | CONST of bool | AND | OR | NOT | XOR | EQ | VAR of string

(* convert a string into a token *)
let token_of_string = function
  | "(" -> OP
  | ")" -> CP
  | "nand" -> NAND
  | "T" -> CONST true
  | "F" -> CONST false
  | "and" -> AND
  | "or" -> OR
  | "not" -> NOT
  | "xor" -> XOR
  | "=" -> EQ
  | s -> if (is_varname s) then (VAR s) else (invalid_arg ("Unknown Token: "^s))

(* convert a list of strings into a a list of tokens *)
let tokens wl : bexp_token list = List.map token_of_string wl

(* type representing a boolean expression, you need to add variants here *)
type boolExpr = Const of bool
| Id of string
| Nand of boolExpr * boolExpr
| And of boolExpr * boolExpr
| Or of boolExpr * boolExpr
| Not of boolExpr
| Xor of boolExpr * boolExpr
| Eq of boolExpr * boolExpr
(*------------------------------------------------END-----------------------------------------------*)



(*-------------------------------------------parse_bool---------------------------------------------*)
(* attempt to turn a list of tokens into a boolean expression tree.
A token list representing a boolean expression is either
 + a CONST token :: <more tokens> or
 + a VAR token :: <more tokens> or
 + an OPEN PAREN token :: a NAND token :: <a token list representing a boolean expression> @
                                          <a token list representing a boolen expression> @ a CLOSE PAREN token :: <more tokens>
 any other list is syntactically incorrect. *)
let parse_bool_exp tok_list =
(* when possibly parsing a sub-expression, return the first legal expression read
   and the list of remaining tokens  *)
  let rec parser tlist = match tlist with
    | (CONST b)::t -> (Const b, t)
    | (VAR s)::t -> (Id s, t)
    | OP::NAND::t -> let (a1, t1) = parser t in (*get the op and recurse through the thing after it*)
                     let (a2, t2) = parser t1 in (*second thing to recurse through*)
                     (match t2 with
                     | CP::t' -> ((Nand (a1,a2)), t') (*check for close paren*)
		     | _ -> invalid_arg "sexp: missing )")
    | OP::AND::t -> let (a1, t1) = parser t in (*get the op and recurse through the thing after it*)
                    let (a2, t2) = parser t1 in (*second thing to recurse through*)
                    (match t2 with
                    | CP::t' -> ((And (a1,a2)), t') (*check for close paren*)
		    | _ -> invalid_arg "sexp: missing )")
    | OP::OR::t -> let (a1, t1) = parser t in (*get the op and recurse through the thing after it*)
                     let (a2, t2) = parser t1 in (*second thing to recurse through*)
                     (match t2 with
                     | CP::t' -> ((Or (a1,a2)), t') (*check for close paren*)
		     | _ -> invalid_arg "sexp: missing )")
    | OP::NOT::t -> let (a1, t1) = parser t in (*get the op and recurse through the thing after it*)
                     (match t1 with
                     | CP::t' -> ((Not (a1)), t') (*check for close paren*)
		     | _ -> invalid_arg "sexp: missing )")
    | OP::XOR::t -> let (a1, t1) = parser t in (*get the op and recurse through the thing after it*)
                     let (a2, t2) = parser t1 in (*second thing to recurse through*)
                     (match t2 with
                     | CP::t' -> ((Xor (a1,a2)), t') (*check for close paren*)
		     | _ -> invalid_arg "sexp: missing )")
    | OP::EQ::t -> let (a1, t1) = parser t in (*get the op and recurse through the thing after it*)
                     let (a2, t2) = parser t1 in (*second thing to recurse through*)
                     (match t2 with
                     | CP::t' -> ((Eq (a1,a2)), t') (*check for close paren*)
		     | _ -> invalid_arg "sexp: missing )")
    | _ -> invalid_arg "parse failed."
  in let bx, t = parser tok_list in
     match t with
     | [] -> bx
     | _ -> invalid_arg "parse failed: extra tokens in input."

(* pipeline from s-expression string to boolExpr *)
let bool_exp_of_s_exp s = s |> wordlist |> tokens |> parse_bool_exp
(*------------------------------------------------END-----------------------------------------------*)



(*------------------------------------------eval_bool_exp-------------------------------------------*)
(* evaluate the boolean expression bexp, assuming the variable names
   in the list tru are true, and variables not in the list are false *)
let rec eval_bool_exp bexp tru =
  match bexp with
  | Const b -> b
  | Id s -> List.mem s tru
  | Nand (x1,x2) -> not ((eval_bool_exp x1 tru) && (eval_bool_exp x2 tru))
  | And (x1,x2) -> (eval_bool_exp x1 tru) && (eval_bool_exp x2 tru)
  | Or (x1,x2) -> (eval_bool_exp x1 tru) || (eval_bool_exp x2 tru)
  | Not (x1) -> not (eval_bool_exp x1 tru)
  | Xor (x1,x2) -> ((not (eval_bool_exp x1 tru)) && (eval_bool_exp x2 tru)) || ((eval_bool_exp x1 tru) && (not (eval_bool_exp x2 tru)))
  | Eq (x1,x2) -> (eval_bool_exp x1 tru) = (eval_bool_exp x2 tru)
  (*this just implements the logical equivalent of the logic statement read in*)
(*------------------------------------------------END-----------------------------------------------*)



(*-----------------------------------------------subsets--------------------------------------------*)
let subsets s = 
 let rec recset l = match l with
  | [] -> [[]] 
  | (h::tl) ->
              let second = recset tl in
              (List.map (fun x -> h::x) second)@second
 in recset s
(*pull off the head and keep track of it to make subsets with the head as the lead*) 
(*conc the head onto a tail including a list of what follows, next time it will be one shorter*)
(*------------------------------------------------END-----------------------------------------------*)



(*----------------------------------------------var_list--------------------------------------------*)
(* find all the variable names in a boolExpr *)

  (*------some filtering functions----------------------------------------------------------------*)  
  (* Removes an element in the list *)
	let remove_elt element lst =
 	let rec tr_remove_elt lst acc = match lst with  
   	| [] -> List.rev acc
   	| h::t -> if (element = h) then tr_remove_elt t acc else tr_remove_elt t (h::acc)
        (*make a new list from the old, if you find element, then skip it*)
  	in tr_remove_elt lst []

  (* Removes duplicates in a list*)
	let remove_duplicates lst =
 	let rec tr_remove_duplicates lst acc = match lst with
 	   | [] -> List.rev acc
 	   | h :: t -> tr_remove_duplicates (remove_elt h t) (h::acc)
           (*pull an element off the list, then look at the rest of the list to see if it's there*)
 	in tr_remove_duplicates lst []
  (*----------------------------------------------------------------------------------------------*)

let var_list bexp =
  let rec helper bexp = match bexp with
    | Const b -> [] (*trues and falses are empty*)
    | Id s -> [s] (*what we are looking for*)
    | Nand (x1,x2) -> remove_duplicates ((helper x1)@(helper x2)) (*append what you find in each*)
    | And (x1,x2) -> remove_duplicates ((helper x1)@(helper x2)) (*append what you find in each*)
    | Or (x1,x2) -> remove_duplicates ((helper x1)@(helper x2)) (*append what you find in each*)
    | Not (x1) -> remove_duplicates ((helper x1)) (*just look inside*)
    | Xor (x1,x2) -> remove_duplicates ((helper x1)@(helper x2)) (*append what you find in each*)
    | Eq (x1,x2) -> remove_duplicates ((helper x1)@(helper x2)) (*append what you find in each*)
  in helper bexp
    (*this outputs only args or empty stuff, treats any connecting phrases as appends*)

(*------------------------------------------------END-----------------------------------------------*)



(*---------------------------------------------find_sat_set-----------------------------------------*)
(* find a list of variables that when set to true make the expression true *)

let find_sat_set bexp: string list option =
  let rec allcombos exp tlst = match tlst with
    | [] -> None 
    | h::t -> if (eval_bool_exp exp h) then Some h (*check with one particular true/false combo*)
              else allcombos bexp t 
    in allcombos bexp (List.rev (subsets (var_list bexp))) 
(*you must check all combinations on the rare condition that the same argument being true and false in an expression changes the meaning of the output eg: x and not x -> true not x. Also, we must check the empty list first to deal with this very case, so reverse var_list*)
(*------------------------------------------------END-----------------------------------------------*)



(*----------------------------------------------sat_main--------------------------------------------*)
(*calls find_sat_set and *)
let sat_main () = 
  let sExpr = String.concat " " (read_lines ()) in (*get input from read_lines*)
  let bExpr = bool_exp_of_s_exp sExpr in (*convert input to bool expression*)
  let result = find_sat_set bExpr in (*get list of satisfied variables*)
  let output = match result with (*make a string out of the string option*)
   | None -> "Not Satisfiable" 
   | Some s -> "Satisfied when the variables {" ^ (String.concat ", " s) ^"} are set to true."
  in print_endline output (*print*)

(*------------------------------------------------END-----------------------------------------------*)



(*------------------------------------------------main----------------------------------------------*)

let main true_vars_list =
  let sExpr = String.concat " " (read_lines ()) in
  let bExpr = bool_exp_of_s_exp sExpr in
  let result = eval_bool_exp bExpr true_vars_list in
  let svarlist = " when the variables {" ^ (String.concat ", " true_vars_list) ^"} are set to true." in
  let output = (if result then "True" else "False")^svarlist in
print_endline output
(*------------------------------------------------END-----------------------------------------------*)
