(* The only explicit recursion in this file should be in this pre-defined function *)
let file_lines fname =
  let in_file = open_in fname in
  let rec loop acc =
    let next_line = try Some (input_line in_file) with End_of_file -> None in
    match next_line with
    | (Some l) -> loop (l::acc)
    | None -> acc
  in
  let lines = try List.rev (loop []) with _ -> [] in
  let () = close_in in_file in
  lines

let file_as_string fname = String.concat "\n" (file_lines fname)

let split_words = Str.split (Str.regexp "\\b") 
