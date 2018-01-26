open Program
open Parser
;;
(* Read the program from a filename provided on the command line*)
if Array.length Sys.argv < 2 then () else
  let infile = open_in Sys.argv.(1) in
  let first_line = input_line infile in (* Allow the unix #! trick on the first line, just for fun *)
  let rec read_loop acc =
    let next_line = try Some (input_line infile) with End_of_file -> None in
    match next_line with
    | Some s -> read_loop (acc^"\n"^s)
    | None -> acc in
  let progString = read_loop (if (String.length first_line > 2) && (String.sub first_line 0 2) = "#!" then "" else first_line) in
  (* Parse the program...*)
  let progExpr = progString |> wordlist |> tokens |> parse_pos
                in
  (* Type check the program; we don't actually care about its type, just that it is valid. *)
  let _ = typeof (const_fold progExpr) [] in
  (* call const_fold on progExpr here, and unused_def_elim on the result of const_fold.  Change the previous line so you can check the type of const_fold progExpr*)
  let result = unused_def_elim (const_fold progExpr) in
  (* Run the program (optimized) program. *)
  let _ = eval result [] in () (* change progExpr to whatever name you bound to (unused_def_elim (const_fold progExpr)) above *)
