open Lwt

(* a list associating user nicknames to the output channels that write to their connections *)
(* Once we fix the other functions this should change to []*)
let sessions = ref []
exception Quit

(*---------------------------------------------SESHYSTREAM------------------------------------------*)

let seshystream = Lwt_mutex.create () (*This thread is used to keep track of when sessions in use*)

(*----------------------------------------------BROADCAST-------------------------------------------*)

(* replace Lwt.return below with code that uses Lwt_list.iter_p to
  print sender: msg on each output channel (excluding the sender's)*)
let rec broadcast sender msg = Lwt_list.iter_p (fun (ooh,ahh) -> if ooh = sender 
                         then Lwt.return () 
                         else Lwt_io.fprintl ahh (sender^": "^msg)) (!sessions)

(*-------------------------------------------REMOVE_SESSION-----------------------------------------*)

(* remove a session from the list of sessions: important so we don't try to
   write to a closed connection *)

let rec remove_session nn = Lwt_mutex.lock seshystream >>= (*lock the sessions stream*)
                              (*below: get rid of the specified session*)
                          fun () -> Lwt.return (sessions := List.remove_assoc nn !sessions) >>=
                          fun () -> broadcast nn "<left chat>" >>= (*bye, suckers*)
                          fun () -> Lwt.return (Lwt_mutex.unlock seshystream)(*done*)

(*--------------------------------------------HANDLE_ERROR------------------------------------------*)

(* Modify to handle the "Quit" case separately, closing the channels before removing the session *)
let handle_error e nn inp outp = match e with
(*quit the user out of the chat by closing in and out streams*)
|Quit -> Lwt_io.close inp >>= 
         fun () -> Lwt_io.close outp >>=
         fun () -> Lwt.return (remove_session nn)
      (*you should probably never get to this point*)
|_ -> Lwt_io.fprintl (List.assoc nn !sessions) "<ohmygodohmygodohmygod>" >>= 
         fun () -> broadcast nn "<I just DIED.>" >>= (*tell people that something went wrong*)
         fun () -> Lwt_io.close inp >>= 
         fun () -> Lwt_io.close outp >>= 
         fun () -> Lwt.return (remove_session nn)

(*---------------------------------------------CHANGE_NN--------------------------------------------*)

let rec change_nn nn outp new_nn = broadcast !nn ("<changed nick to "^new_nn^">") >>=
                              fun () -> Lwt_mutex.lock seshystream >>= (*lock the sessions stream*)
                              (*below: get rid of the specified session*)
 (*remove name from sessions*)fun () -> Lwt.return (sessions := List.remove_assoc !nn !sessions) >>=
                              fun () -> Lwt.return (nn:=new_nn) >>= (*update nickname*)
              (*add new name*)fun () -> Lwt.return (sessions := (new_nn,outp)::(!sessions)) >>=
                              fun () -> Lwt.return (Lwt_mutex.unlock seshystream) (*done*)


(*--------------------------------------------LOGIN_HANDLER-----------------------------------------*)

let rec login_handler nr (inp,outp) = Lwt_io.fprintl outp "Enter initial nick:" >>= 
fun () -> Lwt_io.read_line inp >>= fun ip -> Lwt.return (nr := ip) >>= (*put name into nr*)
fun () -> Lwt_mutex.lock seshystream >>= (*lock the stream to prevent multiple mods*)
fun () -> Lwt.return (sessions := (!nr,outp)::(!sessions)) >>=
fun () -> Lwt.return (Lwt_mutex.unlock seshystream) >>= (*done modding*)
fun () -> broadcast !nr "<joined>"

(*--------------------------------------------HANDLE_INPUT------------------------------------------*)

(* modify handle_input below to detect /q, /n, and /l commands *)
let handle_input nr outp l = 
let bogey = try if (String.length l = 1) then l else (Str.string_before l 2) with _ -> "" in 
(*Above: catch weird bug of one or no characters*)
match (bogey) with
|"/q" -> Lwt_io.flush outp >>= fun () -> Lwt.fail Quit
|"/n" -> change_nn nr outp (Str.string_after l 3)
|"/l" -> Lwt_list.iter_s (fun (ooh,_) -> Lwt_io.fprintl outp ooh) !sessions
|"" -> Lwt.return () (*this is called when someone hits enter with no text*)
|_ -> broadcast !nr l


(*--------------------------------------------CHAT_HANDLER------------------------------------------*)

let chat_handler (inp,outp) =
  let nick = ref "" in
  (* replace () below with call to login_handler *)
  let _ = login_handler nick (inp,outp) in
  let rec main_loop () =
	  Lwt_io.read_line inp >>= handle_input nick outp >>= main_loop in
  Lwt.async (fun () -> Lwt.catch main_loop (fun e -> handle_error e !nick inp outp))

(*------------------------------------------------END-----------------------------------------------*)
