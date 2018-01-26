### I. ``length l = length (reverse l)``
#### Property
&forall; l &isin; 'a list: length l = length (reverse l)

#### Base Case 
P([]): length [] = length (reverse []) = 0 

length (reverse []) = length (list.rev []) (evaluate tail_rev [] [] within reverse, see lemma 1)

#### Inductive case
IH:
Assume that <br>
&forall; l &isin; 'a list: length l = length (reverse l)

If this is true, it should hold that for some (l2 = x::l) &isin; 'a list, x &isin; 'a <br>
length l2 = length (x::l) = 1 + length l = length (reverse l2) 

length (reverse l2) = length (reverse (x::l))

= length (tail_rev (x::l) [])

= length (list.rev (x::l)) (evaluate tailrev (x::l) [] within reverse, see lemma 1)

= length ((list.rev l)@[x]) (equivilent expression in ocaml)

= 1 + length (list.rev l)

= 1 + length l (from our assumption)

w<sup>5</sup>

### II. ``tail_sum l = tail_sum (reverse l)``

#### Property
&forall l &isin; int list: tail_sum l = tail_sum (reverse l)

#### Base Case 
P([]): tail_sum [] = tail_sum (reverse [])

tail_sum (reverse []) = tail_sum [] (evaluate reverse)

= tsum [] 0 (evaluate tail_sum)

= List.fold_left (fun acc a-> acc+a) 0 lst (evaluate tsum, see lemma 2)

= 0 (evaluate List.fold_left)

#### Inductive Case
IH:
Assume that &forall l &isin; int list: tail_sum l = tail_sum (reverse l)

If this is true, then it should hold that for some LL = h::l <br>
tail_sum LL = tail_sum (reverse LL)

let us verify that.

tail_sum LL = tail_sum (h::l)

= tsum (h::l) 0 (evaluate tail sum)

= List.fold_left (fun acc a-> acc+a) 0 h::l (evaluate tsum, see lemma 2)

= h + List.fold_left (fun acc a-> acc+a) 0 l (partial evaluate List.fold_left)

note that also:

tail_sum (reverse LL) = tail_sum (reverse (h::l))

= tail_sum (tail_rev (h::l) []) (evaluate reverse)

= tail_sum (list.rev (h::l)) (see lemma 1)

= tail_sum ((list.rev (l))@[h]) (evaluate list.rev)

= tsum ((list.rev (l))@[h]) 0 (evaluate tail_sum)

= List.fold_left (fun acc a-> acc+a) 0 ((list.rev (l))@[h]) (see lemma 2)

= h + List.fold_left (fun acc a-> acc+a) 0 l (evaluate List.fold_left)

Both expressions simplify to the same thing, therefore the assumption holds.

w<sup>5</sup>

### Lemmas

#### Lemma 1

##### Property
&forall; lst,acc &isin; 'a list: tail_rev lst acc = (list.rev lst)@acc

##### Base Case 
P([]) &forall; acc &isin; 'a list: tail_rev [] acc = acc (evaluate tail_rev)

##### Inductive Case
IH:
Assume that
&forall; lst,acc &isin; 'a list: tail_rev lst acc = (list.rev lst)@acc

If this is true, it should hold that for some (lst2 = x::lst) &isin; 'a list, x &isin; 'a <br>
tail_rev lst2 acc = (list.rev lst2)::acc

Let us verify that.

tail_rev lst2 acc = tail_rev (x::lst) acc

= tail_rev lst (x::acc) (evaluate tail_rev)

= (list.rev lst)@(x::acc) (from our assumption)

= (list.rev lst2)@acc (since x was the first item of lst2)

w<sup>5</sup>

##### Consequences
tail_rev lst [] = (list.rev lst)@[] = list.rev lst

#### Lemma 2

##### Property
&forall; lst &isin; int list, &forall; acc &isin; int: tsum lst acc = List.fold_left (fun acc a-> acc+a) acc lst

##### Base Case
&forall; acc &isin; int: tsum [] acc = List.fold_left (fun acc a-> acc+a) acc []

tsum [] acc = acc (evaluate tsum)

List.fold_left (fun acc a-> acc+a) acc [] = acc (evaluate List.fold_left)

so the base case holds.

##### Inductive Case
IH:
Assume that &forall; lst &isin; int list, &forall; acc &isin; int: tsum lst acc = List.fold_left (fun acc a-> acc+a) acc lst

If this is true, it should then hold that for some LL = h::lst <br>
&forall; acc &isin; int: tsum LL acc = List.fold_left (fun acc a-> acc+a) acc LL

tsum LL acc = tsum (h::lst) acc

= tsum lst (h+acc)

= h + tsum lst acc (acc is eventually returned, and addition is commutative, so this is valid)

= h + (List.fold_left (fun acc a-> acc+a) acc lst) (from the assumption)

note that also: <br>
List.fold_left (fun acc a-> acc+a) acc LL = List.fold_left (fun acc a-> acc+a) acc (h::lst)

= List.fold_left (fun acc a-> acc+a) (h+acc) lst

= h + (List.fold_left (fun acc a-> acc+a) acc lst) (from fun, acc is eventually returned, and addition is commutative)

both functions simplify to the same thing, therefore the assumption holds.

w<sup>5</sup>

