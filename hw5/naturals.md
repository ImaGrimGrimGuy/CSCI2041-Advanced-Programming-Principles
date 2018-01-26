### ``power``
#### Property
&forall; X &isin; float, &forall; n &isin; int: power X n = X<sup>n</sup>

#### Base Case
P(0): &forall; X &isin; float: power X 0 = 1.0 (evaluate power)

= X<sup>0</sup>

#### Inductive Case
IH:
Assume that &forall; X &isin; float, &forall; n &isin; int: power X n = X<sup>n</sup>

If this is true, it should then hold that for some N = n+1 <br>
&forall; X &isin; float: power X N = X<sup>N</sup>

Let us verify that.

power X N = power X (n+1)

= X *. (power X n) (evaluate power)

= X .* X<sup>n</sup> (evaluate power)

= X<sup>n+1</sup>

= X<sup>N</sup>

So the assumption holds.

w<sup>5</sup>

### ``pow_nat``

#### Property
&forall; X &isin; float, &forall; n &isin; nat: power X (to_int n) = pow_nat X n

#### Base Case
P(Zero): &forall; X &isin; float: power X (to_int 0) = pow_nat X 0

pow_nat X Zero = 1.0 (evaluate pow_nat)

power X (to_int Zero) = power X 0

= 1.0 

so the base case is ok.

#### Inductive Case

IH:
Assume that &forall; X &isin; float, &forall; n &isin; nat: power X (to_int n) = pow_nat X n

If this is true, it should hold that for some N = Succ (n)

power X (to_int N) = pow_nat X N

power X (to_int N) = power X (to_int (Succ n))

= power X (1 + (to_int n)) (evaluate to_int)

= X *. (power (to_int n)) (evaluate power)

note that also: <br>
pow_nat X N = pow_nat X (Succ n)

= X *. (pow_nat X n) (evaluate pow_nat)

both sides of the equation simplify to the same thing, so the assumption holds.

### ``less_nat``

#### Property
&forall; m,n &isin; nat: less_nat m n &iff; (to_int m) < (to_int n)

#### Base Case 
P(Zero): &forall; m &isin; nat: less_nat m Zero = false (evaluate less_nat)

#### Inductive Case

IH:
Assume that &forall; _m,n_ &isin; nat: less_nat m n &iff; (to_int m) < (to_int n) <br>
if less_nat m n = true <br>
and (to_int m) < (to_int n) = true <br>

If this is true, then it should hold that for some _nother_ = _Succ n_ <br>
less_nat m nother &iff; (to_int m) < (to_int nother) <br>
if less_nat m nother = true <br>
and (to_int m) < (to_int nother) = true

Let us verify that.

less_nat m nother = less_nat m (Succ n)

= less_nat m n (evaluate less_nat given that m != n)

= true (from the assumption)

Checking the other side of the equation

(to_int m) < (to_int nother) = (to_int m) < (to_int (Succ n))

= (to_int m) < (1 + (to_int n)) (evaluate to_int)

= true (if (to_int m) < (to_int n) = true, then (to_int m) < (1 + (to_int n)) = true as well)

Both sides simplify to the same expression given the same parameters, and thus imply each other. <br> The assumption holds.

w<sup>5</sup>
