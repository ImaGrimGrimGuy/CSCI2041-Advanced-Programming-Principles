# Homework 6: Let's chat

*CSci 2041: Advanced Programming Principles, Fall 2017 (afternoon)*

**Due:** Wednesday, November 29 at 11:59pm

n this problem we'll use the `Lwt` concurrency library; you can find
the documentation [here](https://ocsigen.org/lwt/2.5.0/api/).  To
interact with `Lwt` in `utop`, you'll need to `#require
"lwt.simple-top" ;;` (or add this line to your ocamlinit file) and to
build binaries using `Lwt`, you'll need to use `ocamlfind`. See [here](lwt_intro.md)
for the short introduction to using and building programs with `lwt`.

We're going to build a _server_ that allows people to (text) chat with
each other over the internet.  The protocol will be similar to
[Internet Relay Chat (IRC)](https://en.wikipedia.org/wiki/Internet_Relay_Chat)
with a little less functionality.  Since this is a class homework,
we'll use the command-line program `telnet` for a _client_ instead of
developing a fancier interface.  The file `chatServer.ml` contains a
skeleton for the server we'll develop, and the code to run `chatServer` in in `srvmain.ml`.

Right now, it's pretty boring: if you build and run it using:
```
% ocamlfind ocamlc -package lwt -package lwt.unix -linkpkg -o server str.cma chatServer.ml srvmain.ml
% ./server
```
it will listen for and accept network connections, but won't do anything with the user's
input, or write anything at all.

Ultimately we want to be able to support interactions like the
following:

On the server:
```
hoppernj@atlas (/home/hoppernj/csci2041/repo-hoppernj/hw6) % ocamlfind ocamlc -package lwt -package lwt.unix -linkpkg -o server str.cma chatServer.ml srvmain.ml
hoppernj@atlas (/home/hoppernj/csci2041/repo-hoppernj/hw6) % ./server
```

On Alice's machine:
```
alice@remote06 (/home/alice) % telnet atlas.cselabs.umn.edu 16384
Trying 128.101.38.193...
Connected to atlas.cselabs.umn.edu.
Escape character is '^]'.
Enter initial nick:
alice
bob: <joined>
carol: <joined>
hi everyone!
bob: hi alice.
/n whiterabbit
/l
whiterabbit
carol
bob
bob: ooh nice.
carol: i'm outta here.
carol: <left chat>
bob: rude.
well it's only an example.
/q
Connection closed by foreign host.
```

On Bob's machine:
```
bob@remote08 (/home/bob) % telnet atlas.cselabs.umn.edu 16384
Trying 128.101.38.193...
Connected to atlas.cselabs.umn.edu.
Escape character is '^]'.
Enter initial nick:
bob
carol: <joined>
alice: hi everyone!
hi alice.
alice: <changed nick to whiterabbit>
ooh nice.
carol: i'm outta here.
carol: <left chat>
rude.
whiterabbit: well it's only an example.
whiterabbit: <left chat>
/q
Connection closed by foreign host.
```
On Carol's machine:
```
carol@atlas (/home/carol) % telnet atlas.cselabs.umn.edu 16384
Trying 128.101.38.193...
Connected to atlas.cselabs.umn.edu.
Escape character is '^]'.
Enter initial nick:
carol
alice: hi everyone!
bob: hi alice.
/l
carol
bob
alice
alice: <changed nick to whiterabbit>
bob: ooh nice.
i'm outta here.
/q
Connection closed by foreign host.
```

### `login_handler`

When a user connects to the chat server, srvmain.ml calls the function
`ChatServer.chat_handler` with a pair of `channel` values: the first (`inp`) is
an `input_channel` and the second (`outp`) is an `output_channel`.
The `main_loop` helper function inside the module uses the `Lwt`
*bind* operator `>>=` to read a line of input from `inp` (the user's
network connection) and call `handle_input` with this line when it is
available; whenever the actions initiated by `handle_input` complete,
`>>=` is used to call `main_loop` again.  However, before
`chat_handler` invokes `main_loop`, a few set-up operations should
take place.  Find the line `let _ = ()` in `chat_handler` and replace it
with a call to `login_handler` which will do the following:

+ Print a welcome message to `outp` (using one of the `Lwt_io.print`
  functions) asking the user for a "nick"(name) they will use in the chat
  session. (It's a technical term, honest!)

+ Read the user's nickname from `inp` using `Lwt_io.read_line`. Assign
  the new value to the name `nick`.

+ The `ChatServer` module maintains a reference to an associative list, `sessions`
  mapping each user's nicknames to her output channel (so that when a
  message is sent to other users, she doesn't see her input twice)
  Once we know the user's nickname, update `sessions` to include the
  new user and output channel pair.  (Since it represents shared state, your code should take measures to ensure that `sessions` is not modified by two threads simultaneously)

+ Finally, announce that the user has joined the chat (to any other
  users) by calling `broadcast` with the user's nickname and the
  message `"<joined>"`. (We'll fill in the `broadcast` function next.)

### `broadcast`
Whenever a user enters a message, joins the chat, or leaves the chat,
we'll want to tell the other participants in the chat using the
`broadcast` function.  We could step through the `sessions` list in
order, sending the message to each user once the previous message has
been sent, but this might take a considerable amount of time -- imagine
if one or more users is overseas or using dial-up internet.
Fortunately, `Lwt` provides the useful function `Lwt_list.iter_p`,
which takes a function, applies this function to every time in the
list in parallel "threads", and then waits for all of the threads to
finish before passing `()` to the next thread.  Change `broadcast` to
use `Lwt_list.iter_p` to write a line of the form `sender: message` to
every user but the sender in the `!sessions` associative list.  (The
function passed to `iter_p` should execute `Lwt.return ()` when the
session associated with the `sender` nick is encountered)

At this point we're starting to get a useful server: try building and
running `server`, and in separate terminals (but the same
machine) try `telnet localhost 16384`, entering distinct nicks.  You
should be able to carry out a lively conversation with yourself.
(Recruit a friend if this feels too eccentric) One more tip: you can
end a telnet session on the client side by typing ctrl-] and then
entering q at the telnet prompt.

### Modify `handle_input` and associated helpers
The actual IRC protocol allows a wide variety of actions by users;
we'll support three: q(uit), n(ew nickname), and l(ist users).  Modify
`handle_input` so that it checks to see if the input starts with one
of the following commands:

+ The `quit` command, `/q`: quitting should cause the user's thread to
  close the input and output channels, then remove the user from the
  `sessions` list. Note that `main_loop` is bound to the
  `handle_input` thread, so you'll need to use a nonlocal control flow
  mechanism here.  (Hint: the main body of `chat_handler` calls the
  `handle_error` function with any exceptions that are thrown in the
  `main_loop` thread.)

+ The `newnick` command, `/n`: allows a user to change her `nick` to
  the string following ``/n ``.  You should add code that calls
  `change_nn` with the correct inputs and modify `change_nn` to update
  the session list, notify the other users, and update the `nick`
  reference from `chat_handler`.

+ The list users command, `/l`: lists all users connected to the
  server. Hint: the `Lwt_list.iter_s` function provides a convenient way to
  iterate over the `!sessions` list and perform some action for each
  `(nickname,channel)` pair.

(You might find the library functions `Str.string_after` and
`Str.string_before` useful for this portion of the assignment.)

### Do something fun!

You're almost done with the semester, it's time to do something for fun.  Using
your completed `chatServer.ml` and `srvmain.ml` as a guide, create two
additional files: `funSrv.ml` and `funSrvMain.ml`.  Add an
interesting/fun/useful piece of functionality to the server in  `funSrv.ml`, and
include a comment at the top explaining what libraries your code needs (so we
can build and test it out) and what it does.  (A few ideas: add timestamps to
messages and color-code different users' messages; add support for private
messages from one user to another; add connection logging on the server; support
multiple chat rooms; support registered nicknames...)

## All done!

Don't forget to commit all of your changes to the various files edited
for this homework, and push them to (the `hw6` directory in) your individual class repository
on UMN github:

+ `chatServer.ml`
+ `funSrv.ml`
+ `funSrvMain.ml`

You can always check that your changes have pushed
correctly by visiting the repository page on github.umn.edu.
