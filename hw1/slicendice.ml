(* slicendice.ml - command line "driver" for HW1, CSci 2041-afternoon, Fall 17*)

(* Turn a comma-separated string into a list of ints *)
let parse_rc_list s = List.map int_of_string (Str.split (Str.regexp ",") s)

(* parse the command line arguments and call the main function in tables.ml *)
let rec slice_and_dice arglist transpose clst rlst id od = match arglist with
| [] -> Tables.main transpose clst rlst id od
| "--transpose"::t -> slice_and_dice t true clst rlst id od
| "--idelim"::d::t -> slice_and_dice t transpose clst rlst d od
| "--odelim"::d::t -> slice_and_dice t transpose clst rlst id d
| "--rows"::rstr::t -> slice_and_dice t transpose clst (parse_rc_list rstr) id od
| "--cols"::cstr::t -> slice_and_dice t transpose (parse_rc_list cstr) rlst id od
| _ -> failwith "slice_and_dice: invalid argument format"

(* make the call! *)
let () = slice_and_dice (List.tl (Array.to_list Sys.argv)) false [] [] "," ","
