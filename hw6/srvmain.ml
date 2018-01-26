let port = if Array.length Sys.argv > 1 then int_of_string (Sys.argv.(1)) else 16384		  
let s = Lwt_io.establish_server (Unix.ADDR_INET(Unix.inet_addr_any, port)) ChatServer.chat_handler
let _ = Lwt_main.run (fst (Lwt.wait ()))
let _ = Lwt_io.shutdown_server s (* never executes; you might want to use it in utop, though *)
