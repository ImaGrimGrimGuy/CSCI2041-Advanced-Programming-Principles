let () = if (Array.length Sys.argv) < 3 then print_endline "findsim needs at least two arguments!"
  else begin
  let arglist = List.tl (Array.to_list Sys.argv) in match arglist with
  | "--all"::rlistname::tname::[] ->  Similar.main true rlistname tname
  | rlistname::tname::[] -> Similar.main false rlistname tname
  | _ -> print_endline "usage: findsim [--all] replist_name target_name"
  end
