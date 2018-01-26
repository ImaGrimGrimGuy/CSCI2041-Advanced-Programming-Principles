(*------------------------------------------------EXPLANATION---------------------------------------*)
(*
Libraries:

This Code should run just fine without any extra libraries.


Description of Changes:

-Added functions bootcamp, bootreason, and bootie to allow a moderator to boot people from the chat
by closing their input.

-Changed sessions to store data in the form: (Nickname,(InputChannel,OutputChannel))

-changed sessions to order list in chronological order of who joined the chat.

-Changed handle_input to accept input as a parameter.

-added a /b functionality to handle_input. 

-added a new match case to handle_error to assist in implementation of booting.

Implementation:

If you type /b and then enter, then the code will check if you were the 1st person to join the chat
(and that you have not since changed your Nickname). The chat room will then ask you who you want to
boot (you have to spell their name right), followed by an optional personal message to them. The chat
will boot the person of your choosing by first notifying them with the personalized message or a
default, then closing their input channel when you hit enter again. This throws an error in their 
main_loop, which causes handle_error to force-quit their session. Unfortunately, it does nothing if 
you spell a name wrong. Moderating is a big responsibility...

*)

(*-------------------------------------------------CODE---------------------------------------------*)
open Lwt

(* a list associating user nicknames to the output channels that write to their connections *)
(* Once we fix the other functions this should change to []*)
let sessions = ref []
exception Quit
let getinp (i,_) = i
let getoutp (_,o) = o

(*---------------------------------------------SESHYSTREAM------------------------------------------*)

let seshystream = Lwt_mutex.create () (*This thread is used to keep track of when sessions in use*)

(*----------------------------------------------BROADCAST-------------------------------------------*)

(* replace Lwt.return below with code that uses Lwt_list.iter_p to
  print sender: msg on each output channel (excluding the sender's)*)
let broadcast sender msg = Lwt_list.iter_p (fun (ooh,(_,ahh)) -> if ooh = sender 
                         then Lwt.return () (*don't print to your own channel*)
                         else Lwt_io.fprintl ahh (sender^": "^msg)) (!sessions) (*everyone else sees*)

(*-------------------------------------------REMOVE_SESSION-----------------------------------------*)

(* remove a session from the list of sessions: important so we don't try to
   write to a closed connection *)

let remove_session nn = Lwt_mutex.lock seshystream >>= (*lock the sessions stream*)
                              (*below: get rid of the specified session*)
                          fun () -> Lwt.return (sessions := List.remove_assoc nn !sessions) >>=
                          fun () -> broadcast nn "<left chat>" >>= (*bye, suckers*)
                          fun () -> Lwt.return (Lwt_mutex.unlock seshystream)(*done*)

(*--------------------------------------------HANDLE_ERROR------------------------------------------*)

(* Modify to handle the "Quit" case separately, closing the channels before removing the session *)
let handle_error e nn inp outp = match e with
(*quit the user out of the chat by closing in and out streams*)
|Quit -> Lwt_io.close inp >>= (*close out input and output*)
         fun () -> Lwt_io.close outp >>=
         fun () -> Lwt.return (remove_session nn) (*update sessions*)
      (*you should probably never get to this point*)
|Lwt_io.Channel_closed("input") -> broadcast nn ("<was booted>") >>= (*announce booting*)
         fun () -> Lwt_io.close inp >>= (*purge the booted channel*)
         fun () -> Lwt_io.close outp >>= (*purge the booted channel*)
         fun () -> Lwt.return (remove_session nn) (*remove booted session*)
|e -> Lwt_io.fprintl (getoutp (List.assoc nn !sessions)) "<ohmygodohmygodohmygod>" >>= 
         fun () -> broadcast nn ("<I just DIED because "^(Printexc.to_string e)^".>") >>= 
                   (*Above: bug checking tool*)
         fun () -> Lwt_io.close inp >>= (*purge the bugged channel*)
         fun () -> Lwt_io.close outp >>= (*purge the bugged channel*)
         fun () -> Lwt.return (remove_session nn) (*remove bugged session*)

(*---------------------------------------------CHANGE_NN--------------------------------------------*)

let change_nn nn inp outp new_nn = broadcast !nn ("<changed nick to "^new_nn^">") >>=
                             fun () -> Lwt_mutex.lock seshystream >>= (*lock the sessions stream*)
                             (*below: get rid of the specified session*)
(*remove name from sessions*)fun () -> Lwt.return (sessions := List.remove_assoc !nn !sessions) >>=
                            fun () -> Lwt.return (nn:=new_nn) >>= (*update nickname*)
            (*add new name*)fun () -> Lwt.return (sessions := ((!sessions)@[(new_nn,(inp,outp))])) >>=
                            fun () -> Lwt.return (Lwt_mutex.unlock seshystream) (*done*)


(*--------------------------------------------LOGIN_HANDLER-----------------------------------------*)

let login_handler nr (inp,outp) = Lwt_io.fprintl outp "Enter initial nick:" >>= 
fun () -> Lwt_io.read_line inp >>= fun ip -> Lwt.return (nr := ip) >>= (*put name into nr*)
fun () -> Lwt_mutex.lock seshystream >>= (*lock the stream to prevent multiple mods*)
fun () -> Lwt.return (sessions := ((!sessions)@[(!nr,(inp,outp))])) >>=
fun () -> Lwt.return (Lwt_mutex.unlock seshystream) >>= (*done modding*)
fun () -> broadcast !nr "<joined>"

(*------------------------------------------------BOOTIE--------------------------------------------*)

let bootie nr outp inp id = Lwt_io.flush outp >>=
 fun () -> Lwt_io.flush (getoutp (List.assoc id !sessions)) >>= (*flush channels to be safe*)
 fun () -> Lwt_io.close (getinp (List.assoc id !sessions)) (*cause an error in the offender's login*)

(*----------------------------------------------BOOTREASON------------------------------------------*)

let bootreason nr outp inp id = Lwt_io.fprintl outp "(optional) is there anything you would like to tell this person before they go?" >>=
                  fun () -> Lwt_io.read_line inp >>= (*personal message*)
                  fun re -> match re with 
                  |"" -> Lwt_io.fprintl (getoutp (List.assoc id !sessions)) "You have been booted" >>=
                         fun () -> bootie nr outp inp id (*default case for when there's no message*)
                  |s -> Lwt_io.fprintl (getoutp (List.assoc id !sessions)) s >>=
                        fun () -> bootie nr outp inp id (*personal message and call to bootie*)

(*-----------------------------------------------BOOTCAMP-------------------------------------------*)

let bootcamp nr outp inp = if (!nr = (getinp (List.hd !sessions)))(*mod is the 1st in sessions*)
                         then (let boot () = Lwt_io.fprintl outp "Who would you like to boot?" >>=
                               fun () -> Lwt_io.read_line inp >>= fun id -> bootreason nr outp inp id in
                                         Lwt.async (fun () -> Lwt.catch boot (fun _ -> Lwt.return())))
                                   (*above: try call message function, go back to handle_input 
                                     if name isn't found in sessions*)
                         else (let boot () = Lwt_io.fprintl outp "You are not classified as moderator" in
                                             Lwt.async (fun () -> Lwt.catch boot (fun _ -> Lwt_io.fprintl outp "how did we get here..." >>=
                                             (*above: you should never get to this point*)
                                                                  fun () -> Lwt.return ())))

(*--------------------------------------------HANDLE_INPUT------------------------------------------*)

(* modify handle_input below to detect /q, /n, and /l commands *)
let handle_input nr outp inp l = 
let bogey = try if (String.length l = 1) then l else (Str.string_before l 2) with _ -> "" in 
(*Above: catch weird bug of one or no characters*)
match (bogey) with
|"/q" -> Lwt_io.flush outp >>= fun () -> Lwt.fail Quit (*raise exception in main_loop*)
|"/n" -> change_nn nr inp outp (Str.string_after l 3) (*call change_ nn with stuff after /n*)
|"/l" -> Lwt_list.iter_s (fun (ooh,_) -> Lwt_io.fprintl outp ooh) !sessions (*print out the peeps*)
|"/b" -> Lwt.return (bootcamp nr outp inp) (*booting*)
|"" -> Lwt.return () (*this is for the case that someone hits return with no input*)
|_ -> broadcast !nr l

(*--------------------------------------------CHAT_HANDLER------------------------------------------*)

let chat_handler (inp,outp) =
  let nick = ref "" in
  (* replace () below with call to login_handler *)
  let _ = login_handler nick (inp,outp) in
  let rec main_loop () =
	  Lwt_io.read_line inp >>= handle_input nick outp inp >>= main_loop in
  Lwt.async (fun () -> Lwt.catch main_loop (fun e -> handle_error e !nick inp outp))

(*------------------------------------------------END-----------------------------------------------*)
