open Program

(* small example programs:
   Because we're keeping type inference simple, we'll require functions to have a single argument,
   and declare the type of that argument after a colon.
   To simplify parsing function applications, we'll have explicit "app" expressions, so to apply function f to argument x,
   the program will say (app f x).  A multiple argument function will need to be applied to each argument in turn, so the equivalent to the
   Ocaml expression (f x y) will be (app (app f x) y).
*)
let example1 =
  "(let f (fun g : int -> int  (app g 0))
          (print (app f (fun x : int (+ x 2)))))"

let example2 =
  "(let gcd (fun a : int (fun b : int
            (let q (/ a b)
            (let r (- a (* q b))
                   (seq (while (not (= r 0))
                               (seq (set a b)
                                    (set b r)
                                    (set q (/ a b))
                                    (set r (- a (* q b)))))
                         b)))))
            (print (app (app gcd 217) 527)))"

let example3 =
"(let y 0
    (let x (+ 1 2)
        (while (> x 0)
            (seq
                (set x (- x 1))
                (if (> 1 0) x y)
                (if (< 1 0) x y)
                (while (> 1 0) (print y))
                (+ 1 2)
                (seq (let z (+ 2 3) (< 1 2)))
            )
        )
    )
)"

(* the first let z cannot be eliminated here because its definition contains a side effect *)
let example4 =
"(let y (* 0 0)
  (let z (if (> y 4)
           (seq (set y (- y 1)) 1)
           0)
    (seq (print y)
         (if (= (+ 1 0) (- 2 1))
             (let z readint z)
             (+ 42 17)))
  )
)"

(* notice the second z "shadows" the first, so the first let z can be eliminated here *)
(* the second cannot, because of the side effect in the definition and its use of z in the body *)
let example5 =
"(let y (- 0 0)
  (let z (if (> y 4) 1 0)
    (seq (print y)
         (if (= (+ 1 0) (- 2 1))
             (let z readint z)
             (+ 42 17)))
  )
)"


(* all of the lexical tokens we might encounter in a program *)
type token = OP | CP | AND | OR | NOT | PLUS | MINUS | TIMES | DIV | LET | ID of string | CONST of int | BCONST of bool | LT | GT | EQ | IF |
	     SET | SEQ | WHILE | PRINT |
	     APP | FUN | COLON | ARROW | INT | BOOL | UNIT | READ

(* Split a string into a list of words, delimited by spaces, parens, colons, and -> *)
(* never mind the magic regexp *)
let wordlist s =
  let splitlist = Str.full_split (Str.regexp "\\b\\|(\\|)\\|:\\|\\(->\\)") s in
  let rec filter_splist lst = match lst with
    | [] -> []
    | (Str.Delim "(")::t -> "(" :: (filter_splist t)
    | (Str.Delim ")")::t -> ")" :: (filter_splist t)
    | (Str.Delim "->")::t -> "->" :: (filter_splist t)
    | (Str.Delim ":")::t -> ":"::(filter_splist t)
    | (Str.Delim _) :: t -> filter_splist t
    | (Str.Text s) :: t -> let s' = String.trim s in
                           let t' = (filter_splist t) in
                           if not (s' = "") then s' :: t' else t'
  in filter_splist splitlist

(* turn a word into a token *)
let tokenize_string = function
  | "(" -> OP
  | ")" -> CP
  | "and" -> AND
  | "or" -> OR
  | "not" -> NOT
  | "+" -> PLUS
  | "*" -> TIMES
  | "-" -> MINUS
  | "/" -> DIV
  | "let" -> LET
  | ">" -> GT
  | "<" -> LT
  | "=" -> EQ
  | "if" -> IF
  | "set" -> SET
  | "seq" -> SEQ
  | "while" -> WHILE
  | "app" -> APP
  | "fun" -> FUN
  | ":" -> COLON
  | "->" -> ARROW
  | "int" -> INT
  | "bool" -> BOOL
  | "unit" -> UNIT
  | "print" -> PRINT
  | "true" -> BCONST true
  | "false" -> BCONST false
  | "readint" -> READ
  | s -> if Str.string_match (Str.regexp "[0-9]+") s 0 then (CONST (int_of_string s))
	 else if Str.string_match (Str.regexp "[a-z]+") s 0 then (ID s) else failwith ("invalid token:"^s)

(* and a list of words into a list of tokens *)
let tokens wl = List.map tokenize_string wl

(* Parse a type expression in a function definition.
   Return the type and the list of unused tokens for further parsing.
   A type expression is either: INT, BOOL, UNIT or  (typeExpr)  or typeExpr -> typeExpr  *)
let rec parse_type_expr tlist =
  let (ty1, tl) =
    match tlist with
    | INT::t -> (Int,t)
    | BOOL::t -> (Bool,t)
    | UNIT::t -> (Unit,t)
    | OP::t -> (* Read up until we find a close paren: covers types like "(int->bool) -> int" *)
       let (ty,t) = parse_type_expr t in
       ( match t with
	 | CP::t' -> (ty,t')
	 | _ -> failwith "imbalanced parentheses in type expression" )
    | _ -> failwith "unexpected token in type expression."
  in match tl with (* peek at tail: is there an arrow (so more type expr to read)? *)
     | ARROW::t1 ->
	let (ty2, t2) = parse_type_expr t1 in (FunType(ty1,ty2),t2)
     | _ -> (ty1,tl) (* No, we're done here. *)

let parse_program tlist =
  (* parse an expression from a list of tokens, returning the expression and the list of unused tokens *)
  let rec parser tlist = match tlist with
    | [] -> failwith "Ran out of tokens without closing parenthesis"
    | (BCONST b)::t -> (Boolean b,t)
    | (CONST i)::t -> (Const i, t)
    | (ID s)::t -> (Name s, t)
    | OP::PLUS::t -> let (e1,e2,t') = parse_two t in (Add (e1,e2), t')
    | OP::MINUS::t -> let (e1,e2,t') = parse_two t in (Sub (e1,e2), t')
    | OP::TIMES::t -> let (e1,e2,t') = parse_two t in (Mul (e1,e2), t')
    | OP::DIV::t -> let (e1,e2,t') = parse_two t in (Div (e1,e2), t')
    | OP::AND::t -> let (e1,e2,t') = parse_two t in (And (e1,e2), t')
    | OP::OR::t -> let (e1,e2,t') = parse_two t in (Or (e1,e2), t')
    | OP::EQ::t -> let (e1,e2,t') = parse_two t in (Eq (e1,e2), t')
    | OP::GT::t -> let (e1,e2,t') = parse_two t in (Gt (e1,e2), t')
    | OP::LT::t -> let (e1,e2,t') = parse_two t in (Lt (e1,e2), t')
    | OP::WHILE::t -> let (e1,e2,t') = parse_two t in (While (e1,e2), t')
    | OP::APP::t -> let (e1,e2,t') = parse_two t in (Apply (e1,e2), t')
    | OP::FUN::(ID s)::COLON::t ->
       let (tExp, t') = parse_type_expr t in
       let (bExp,t'') = parse_single t' in (Fun (s,tExp,bExp),t'')
    | OP::LET::(ID s)::t -> let (v,e,t') = parse_two t in (Let (s,v,e), t')
    | OP::SET::(ID s)::t -> let (e,t') = parse_single t in (Set (s,e), t')
    | OP::IF::t ->
       let (c,t1) = parser t in
       let (thn,els,t2) = parse_two t1 in (If (c,thn,els), t2)
    | OP::NOT::t -> let (e,t') = parse_single t in (Not(e),t')
    | OP::PRINT::t -> let (e,t') = parse_single t in (Print(e), t')
    | OP::SEQ::t -> let (l,t') = parse_list t in (Seq(l),t')
    | READ::t -> (Readint, t)
    | _ -> failwith "Unexpected token: unbalanced parentheses or keyword out of call position"

  and parse_single t = let (e,t') = parser t in  (* parse a single expression and "eat" the following close paren *)
    ( match t' with
      | CP::t'' -> (e,t'')
      | _ -> failwith "parser: missing closing paren.") 
  and parse_two t = (* "eat" the close paren after two expressions *)
    let (e1,t1) = parser t in
    let (e2,t2) = parser t1 in
    ( match t2 with
      | CP::t' -> (e1,e2,t')
      | _ -> failwith "parser: missing closing paren.")
  and parse_list t = (* parse a list of expressions, consuming the final closing paren *)
    ( match t with
      | CP::t' -> ([],t')
      | [] -> failwith "unfinished expression sequence: missing close paren(s)."
      | _ -> let (e,t1) = parser t in
	     let (el,t2) = parse_list t1 in (e::el, t2)
    )
  in
  let (e,t) = parser tlist in
  match t with
  | [] -> e
  | _ -> failwith "parse failed: extra tokens in input."

(*---------------------------------------------const_fold-------------------------------------------*)
let const_fold (e : expr) = 
  let rec smush exp = match exp with
    | Const n -> Const n 
    | Boolean b -> Boolean b
    | Add (e1,e2) -> (match (smush e1,smush e2) with
                       |(Const i1,Const i2) -> Const (i1+i2) (*math is amazing*)
                       |(_,_) -> Add (smush e1,smush e2))
    | Mul (e1,e2) -> (match (smush e1,smush e2) with 
                       |(Const i1,Const i2) -> Const (i1*i2) (*math is amazing*)
                       |(_,_) -> Mul (smush e1,smush e2))
    | Sub (e1,e2) -> (match (smush e1,smush e2) with
                       |(Const i1,Const i2) -> Const (i1-i2) (*math is amazing*)
                       |(_,_) -> Sub (smush e1,smush e2))
    | Div (e1,e2) -> (match (smush e1,smush e2) with
                       |(Const i1,Const i2) -> Const (i1/i2) (*math is amazing*)
                       |(_,_) -> Div (smush e1,smush e2))
    | If (cond,thn,els) -> (match (smush cond) with (*if true and if false*)
                             | (Boolean true) -> smush thn (*if true then*)
                             | (Boolean false) -> smush els(*if false else*)
                             | _ -> If(cond,smush thn,smush els))
    | Let (nm,vl,exp') -> (match (smush vl,smush exp') with
                           |(_,Const b) -> Const b (*rename x const to y const -> y const*)
                           |(_,Boolean b) -> Boolean b (*rename x bool to y bool -> y bool*)
                           |(_,_) -> Let(nm,smush vl, smush exp'))
    | Name nm -> Name nm 
    | And (e1,e2) -> (match (smush e1,smush e2) with (*false and _ = false*)
                       |(_,Boolean false) -> Boolean false
                       |(Boolean false,_) -> Boolean false
                       |(_,_) -> And (smush e1,smush e2))
    | Or (e1,e2) -> (match (smush e1,smush e2) with (*true or _ = true*)
                       |(_,Boolean true) -> Boolean true
                       |(Boolean true,_) -> Boolean true
                       |(_,_) -> Or (smush e1,smush e2))
    | Not e -> Not (smush e)
    | Lt (e1, e2) -> (match (smush e1,smush e2) with 
                       |(Const a,Const b) -> Boolean (a<b) (*comparisons are amazing*)
                       |(_,_) -> Lt (smush e1, smush e2)) 
    | Eq (e1, e2) -> (match (smush e1,smush e2) with 
                       |(Const a,Const b) -> Boolean (a=b) (*comparisons are amazing*)
                       |(_,_) -> Eq (smush e1, smush e2))
    | Gt (e1, e2) -> (match (smush e1,smush e2) with 
                       |(Const a,Const b) -> Boolean (a>b) (*comparisons are amazing*)
                       |(_,_) -> Gt (smush e1, smush e2))
    | Seq elist -> smushSeq (elist) (*call fun for Seq types*)
    | While (cond,body) -> if (smush cond) = (Boolean false) then Seq [] else While (smush cond,smush body)
    | Set (name, e) -> Set (name, smush e)
    | Fun (argname,a,body) -> Fun (argname,a,smush body)
    | Apply (f,e) -> Apply (smush f,smush e)
    | Print e -> Print (smush e)
    | Readint -> Readint
  and smushSeq el = match (List.rev el) with (*pull off the last item by flipping*)
    | [] -> Seq [] (*empty Seq has no handling*)
    | h::t -> match t with
        |[] -> smush h (*for when there is only one thing left*)
        |_ -> if (List.length (List.rev ((smush h)::(List.filter (filfun) (List.map smush (t))))) > 1)
              then (Seq (List.rev ((smush h)::(List.filter (filfun) (List.map smush (t))))))
              else smush h
               (* ^ filter consts from a list that has been simplified with smush, keep last*)
               (*if there is only one item on the list left, just return that item*)
  and filfun = function (*predicate for filter function*)
    | Boolean _ -> false
    | Const _ -> false
    | _ -> true
  in smush e


(*------------------------------------------unused_def_elim-----------------------------------------*)
let unused_def_elim e = 
  let rec ghostbuster e = match e with
  (*step through the expression, preserving form*)
  | Const c -> Const c
  | Boolean b -> Boolean b
  | Name nm -> Name nm
  | Not e -> Not (ghostbuster e)
  | Print e -> Print (ghostbuster e)
  | Add (e1,e2) -> Add (ghostbuster e1,ghostbuster e2)
  | Sub (e1,e2) -> Sub (ghostbuster e1,ghostbuster e2)
  | Mul (e1,e2) -> Mul (ghostbuster e1,ghostbuster e2)
  | Div (e1,e2) -> Div (ghostbuster e1,ghostbuster e2)
  | And (e1,e2) -> And (ghostbuster e1,ghostbuster e2)
  | Or (e1,e2) -> Or (ghostbuster e1,ghostbuster e2)
  | Lt (e1,e2) -> Lt (ghostbuster e1,ghostbuster e2)
  | Eq (e1,e2) -> Eq (ghostbuster e1,ghostbuster e2)
  | Gt (e1,e2) -> Gt (ghostbuster e1,ghostbuster e2)
  | If (c,thn,els) -> If (ghostbuster c,ghostbuster thn,ghostbuster els)
  (*special case, need to check some things in proclet helper function*)
  | Let (nm, v, b) -> proclet nm v b
  | Seq elist -> Seq (List.map ghostbuster elist) (*go through the list in Seq*)
  | While (cond,body) -> While (ghostbuster cond,ghostbuster body)
  | Set (name, e) -> Set (name, ghostbuster e)
  (*special case, need to check some things in procfun helper function*)
  | Fun (argname,a,body) -> procfun argname a body
  | Apply (f,e) -> Apply (ghostbuster f,ghostbuster e)
  | Print e -> Print (ghostbuster e)
  | Readint -> Readint
(*process let statements*)
  and proclet nm v b = match v with
    (*if there is a function as v, then see if it is a function that is referenced in b*)
    | Fun (argname,a,body) -> if (not (uses argname b))
                              (*the function wasn't referenced*) 
                              then (ghostbuster b) 
                              (*the function was referenced*)
                              else (Let (nm,ghostbuster v,ghostbuster b))
(*if there isn't a function as v, then check if v isn't referenced in b and if it has no side effect*)
    | _ -> if (not (side_effect v)) && (not (uses nm b)) 
           (*if so, ignore v *)
           then ghostbuster b 
           (*or don't, that's cool too*)
           else Let(nm, ghostbuster v, ghostbuster b)
(*process functions, delete if argname is in body and if there are no side effects in the body*)
  and procfun argname a body = if (uses argname body) && (not (side_effect body)) 
                               (*argname is in the body and the body has no side effects*)
                               then (ghostbuster body) 
                               (*conditions are not met*)
                               else Fun (argname,a,ghostbuster body)
  and side_effect b = match b with (* sees if the function has a side effect on the expression *)
       | Set _ -> true (* These cases are explictly said to be true *)
       | Print _ -> true
       | Readint -> true
       | Apply _ -> true
       | Readint -> true
       (*all these cases just make recursive calls to side_effect and seek trues*)
       | Let(x,y,z) -> side_effect y || side_effect z 
       | Fun(x,y,z) -> side_effect z
       | Seq elist -> List.exists (side_effect) elist (*is there a true in elist?*)
       | Set(x,y) -> side_effect y
       | While(cond, body) -> side_effect cond || side_effect body
       | If(x,y,z) -> side_effect y || side_effect z
       | Not e -> side_effect e
       | And(e1,e2) -> side_effect e1 || side_effect e2
       | Or(e1,e2) -> side_effect e1 || side_effect e2
       | Add(e1,e2) -> side_effect e1 || side_effect e2
       | Sub(e1,e2) -> side_effect e1 || side_effect e2
       | Div(e1,e2) -> side_effect e1 || side_effect e2
       | Mul(e1,e2) -> side_effect e1 || side_effect e2
       | Lt(e1,e2) -> side_effect e1 || side_effect e2
       | Eq(e1,e2) -> side_effect e1 || side_effect e2
       | Gt(e1,e2) -> side_effect e1 || side_effect e2
       | Name nm -> false (* Name will be false *)
       | Const c -> false (* all constants will be false *)
       | Boolean b -> false
       | _ -> failwith "not a supported expression" (*match fail*)
  and uses a b = match b with (*check if name a is shadowbound*)
       | Let(x,y,z) -> if a = x then false else uses a y || uses a z (*a is shadowbound if it is x*)
       | Fun(x,y,z) -> if a = x then true else uses a z (*a is shadowbound if it is x*)
       | Seq elist -> (List.exists (uses a) elist)
       | Name nm -> a = nm (*a is shadowbound*)
       | Set(x,y) -> if a = x then true else uses a y (*a is shadowbound if if is x*)
       (*all these cases just make recursive calls to uses and seek trues*)
       | While(cond,body) -> uses a cond || uses a body 
       | If(x,y,z) ->  uses a y || uses a z
       | Apply(f,e) -> uses a f || uses a e
       | Not e -> uses a e
       | Print e -> uses a e
       | And(e1,e2) -> uses a e1 || uses a e2
       | Or(e1,e2) -> uses a e1 || uses a e2
       | Add(e1,e2) -> uses a e1 || uses a e2
       | Sub(e1,e2) -> uses a e1 || uses a e2
       | Div(e1,e2) -> uses a e1 || uses a e2
       | Mul(e1,e2) -> uses a e1 || uses a e2
       | Lt (e1,e2) -> uses a e1 || uses a e2
       | Eq (e1,e2) -> uses a e1 || uses a e2
       | Gt (e1,e2) -> uses a e1 || uses a e2
       (* All constants will be false *)
       | Const c -> false 
       | Boolean b -> false
       | Readint -> true
       | _ -> failwith "not a supported expression" (*match fails*)
  in ghostbuster e

(*--------------------------------------------parse_pos---------------------------------------------*)
exception SyntaxError of int
exception Unused of int
exception Unclosed of int

let parse_pos input =
    let rec parser_pos tlist count = match tlist with
      | [] -> raise (Unclosed count) (*say a paren is unclosed at the argument you're on*)
      | (BCONST b)::t -> (Boolean b,t)
      | (CONST i)::t -> (Const i, t)
      | (ID s)::t -> (Name s, t)
      (*for all of these, increment a counter to keep track of what argument you are at*)
      (*look for tokens and call the appropriate error checking helper function*)
      | OP::PLUS::t -> let (e1,e2,t') = parse_two t (count + 1) in (Add (e1,e2), t')
      | OP::MINUS::t -> let (e1,e2,t') = parse_two t (count + 2) in (Sub (e1,e2), t')
      | OP::TIMES::t -> let (e1,e2,t') = parse_two t (count + 2) in (Mul (e1,e2), t')
      | OP::DIV::t -> let (e1,e2,t') = parse_two t (count + 2) in (Div (e1,e2), t')
      | OP::AND::t -> let (e1,e2,t') = parse_two t (count + 2) in (And (e1,e2), t')
      | OP::OR::t -> let (e1,e2,t') = parse_two t (count + 2) in (Or (e1,e2), t')
      | OP::EQ::t -> let (e1,e2,t') = parse_two t (count + 2) in (Eq (e1,e2), t')
      | OP::GT::t -> let (e1,e2,t') = parse_two t (count + 2) in (Gt (e1,e2), t')
      | OP::LT::t -> let (e1,e2,t') = parse_two t (count + 2) in (Lt (e1,e2), t')
      | OP::WHILE::t -> let (e1,e2,t') = parse_two t (count + 2) in (While (e1,e2), t')
      | OP::APP::t -> let (e1,e2,t') = parse_two t (count + 2) in (Apply (e1,e2), t')
      | OP::FUN::(ID s)::COLON::t ->
         let (tExp, t') = parse_type_expr (t) in
         let (bExp,t'') = parse_single t' (count + 1) in (Fun (s,tExp,bExp),t'')
      | OP::LET::(ID s)::t -> let (v,e,t') = parse_two t (count + 2) in (Let (s,v,e), t')
      | OP::SET::(ID s)::t -> let (e,t') = parse_single t (count + 1) in (Set (s,e), t')
      | OP::IF::t ->
         let (c,t1) = parser_pos t (count + 1) in
         let (thn,els,t2) = parse_two t1 (count + 2) in (If (c,thn,els), t2)
      | OP::NOT::t -> let (e,t') = parse_single t (count + 1) in (Not(e),t')
      | OP::PRINT::t -> let (e,t') = parse_single t (count + 1) in (Print(e), t')
      | OP::SEQ::t -> let (l,t') = parse_list t (count + (List.length t)) in (Seq(l),t')
      | READ::t -> (Readint, t)
      | _ -> raise (SyntaxError (count))

    and parse_single t count= let (e,t') = parser_pos t (count) in
      ( match t' with
        | CP::t'' -> (e,t'')
        | _ -> raise (Unclosed (count+1)))(*checks if a single value expression is closed*)

    and parse_two t count = let (e1,t1) = parser_pos t (count+1) in
      let (e2,t2) = parser_pos t1 (count) in
      ( match t2 with
        | CP::t' -> (e1,e2,t')
        | [] -> raise (Unclosed (count+2)) (*unclosed error after 2 arguments*)
        | _ -> raise (Unclosed (count+1)) (*unclosed error after just 1 argument*)
        )
        
        and parse_list t count = 
      ( match t with
        | CP::t' -> ([],t') (*special case for Seq*)
        | [] -> raise (Unclosed count)
        | _ -> let (e,t1) = parser_pos t (count + (List.length t)) in
         let (el,t2) = parse_list t1 count in (e::el, t2)(*iterate through Seq and count the things*)
      )
    in
    let (e,t) = parser_pos input 1 in
    (*unused expressions,check length t against input to see if there is extra*)
    match t with
    | [] -> e
    | _ -> raise (Unused ((List.length input)-(List.length t))) 
