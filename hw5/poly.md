### I. ``deg (compose p1 p2) = (deg p1)*(deg p2)``

#### Base Cases
&forall p2 &isin; polyExpr:

P(Int_): deg (compose (Int _) p2) = deg Int _ (evaluate compose) 

= 0

= 0 * (deg p2)

= (deg (Int _)) * (deg p2)

w<sup>5</sup>

P(X): deg (compose X p2) = deg p2 (evaluate compose)

= 1 * (deg p2)

= (deg X) * (deg p2)

w<sup>5</sup>

#### Lemma: max ((deg p1)*(deg p3))((deg p2)*(deg p3)) = (max (deg p1) (deg p2))*(deg p3)
for some c1,c2,c3 &isin; int, such that: <br>
deg p1 = c1 (deg has type polyExp -> int) <br>
deg p2 = c2 (deg has type polyExp -> int) <br>
deg p3 = c3 (deg has type polyExp -> int) <br>

max ((deg p1)*(deg p3)) ((deg p2)*(deg p3)) = max (c1*c3) (c2*c3)

= (c1*c3)||(c2*c3) (evaluate max)

= (c1||c2)*c3 (distributive property of multiplication and "or")

= (max c1 c2)*c3 (reverse evaluate max)

= (max (deg p1) (deg p2))*(deg p3) (from the definitions of c1,c2, and c3)

w<sup>5</sup>

#### Inductive Cases
Assume: <br>
&forall; p1,p2,e1,e2 &isin; polyExpr: deg (compose p1 p2) = (deg p1)*(deg p2)

Then it should hold that:

For the case of p1 = Add (e1, e2): <br>
deg (compose (Add (e1, e2)) p2) = deg (Add (compose e1 p2, compose e2 p2)) (evaluate compose)

= (max (deg (compose e1 p2)) (deg (compose e1 p2))) (evaluate deg)

= max ((deg e1)*(deg p2)) ((deg e2)*(deg p2)) (from our inductive assumption)

= (max (deg e1) (deg e2))*(deg p2) (from Lemma)

= (deg (Add (e1,e2)))*(deg (p2)) (reverse evaluate deg)

= (deg p1)*(deg p2) (recall how p1 was defined for this case)

w<sup>5</sup>

For the case of p1 = Mul (e1, e2): <br>
deg (compose (Mul (e1, e2)) p2) = deg (Mul (compose e1 p2, compose e2 p2)) (evaluate compose)

= (max (deg (compose e1 p2)) (deg (compose e1 p2))) (evaluate deg)

= max ((deg e1)*(deg p2))((deg e2)*(deg p2)) (from our inductive assumption)

= (max (deg e1) (deg e2))*(deg p2) (from Lemma)

= (deg (Mul (e1,e2)))*(deg (p2)) (reverse evaluate deg)

= (deg p1)*(deg p2) (recall how p1 was defined for this case)

w<sup>5</sup>

### II. ``deg (simplify p) <= deg p``

#### Base Cases
P(Int_): deg (simplify (Int _)) <= deg (Int _) = 0 

deg (simplify (Int _)) = deg (Int _) (evaluate simplify)

= 0 (evaluate deg)

P(X): deg (simplify X) <= deg X = 1

deg (simplify X) = deg X (evaluate simplify)

= 1 (evaluate deg)

####Inductive Cases
Assume: <br>
&forall; p,p1,p2 &isin; polyExpr: deg (simplify p) <= deg p

Then it should hold that: 

##### For the case of p = Add (p1,p2):
Our assumption becomes: <br>
deg (simplify (Add (p1,p2))) <= deg (Add (p1,p2))

Simplifying this, we find: <br>
deg (simplify (Add (p1,p2))) = deg (simp_add (simplify p1,simplify p2)) (evaluate simplify)

###### Then, for the sub-case that (simplify p1,simplify p2) = (Int 0, simplify p2)
deg (simplify (Add (p1,p2))) = deg (simplify p2) (evaluate simp_add)

Note that also:
deg (Add (p1,p2)) = max (deg p1) (deg p2) (evaluate deg)

Because of the way that "max" works, we can infer that: <br>
deg (simplify p2) <= max (deg (simplify p1)) (deg (simplify p2)) <= max (deg p1) (deg p2)

since, by our assumption that deg (simplify p) <= deg p, we know that: <br>
deg (simplify p1) <= deg p1 <br>
and <br>
deg (simplify p2) <= deg p2 <br>

Thus: <br>
deg (simplify (Add (Int 0,p2))) <= deg (Add (Int 0,p2))

###### Then, for the sub-case that (simplify p1,simplify p2) = (simplify p1, Int 0)
deg (simplify (Add (p1,p2))) = deg (simplify p1) (evaluate simp_add)

Note that also:
deg (Add (p1,p2)) = max (deg p1) (deg p2) (evaluate deg)

Because of the way that "max" works, we can infer that: <br>
deg (simplify p1) <= max (deg (simplify p1)) (deg (simplify p2)) <= max (deg p1) (deg p2)

since, by our assumption that deg (simplify p) <= deg p, we know that: <br>
deg (simplify p1) <= deg p1 <br>
and <br>
deg (simplify p2) <= deg p2 <br>

Thus: <br>
deg (simplify (Add (p1,Int 0))) <= deg (Add (p1,Int 0))

###### Then, for the sub-case that (simplify p1,simplify p2) = (Int i1,Int i2)
deg (simplify(Add (Int i1,Int i2))) = deg (Int (i1+i2)) (evaluate simp_add)

= 0

note that also: <br>
deg (Add (Int i1,Int i2)) = max (deg (Inti1)) (deg (Int i2)) (evaluate deg)

= max 0 0 = 0

This shows that: <br>
deg (simplify(Add (Int i1,Int i2))) = deg (Add (Int i1,Int i2)) = 0

Thus: <br>
- deg (simplify (Add (Int i1,Int i2))) = deg (Add (Int i1,Int i2))

###### Then, for the sub-case that (simplify p1,simplify p2) = (simplify p1,simplify p2)
deg (simplify(Add (pe1,pe2)) = deg(Add (simplify p1,simplify p2)) (evaluate simp_add)

= max (deg (simplify p1)) (deg (simplify p2)) (evaluate deg)

note that also: <br>
deg (Add (p1,p2)) = max (deg p1) (deg p2) (evaluate deg)

Because of the way that "max" works, we can infer that: <br>
deg (simplify p1) <= max (deg (simplify p1)) (deg (simplify p2)) <= max (deg p1) (deg p2)

since, by our assumption that deg (simplify p) <= deg p, we know that: <br>
deg (simplify p1) <= deg p1 <br>
and <br>
deg (simplify p2) <= deg p2 <br>

Thus: <br>
deg (simplify (Add (p1,p2))) <= deg (Add (p1,p2))

###### Generalizing all of these sub-cases:
Since in the sub-cases we find that:
- deg (simplify (Add (Int 0,p2))) <= deg (Add (Int 0,p2))
- deg (simplify (Add (p1,Int 0))) <= deg (Add (p1,Int 0))
- deg (simplify (Add (Int i1,Int i2))) = deg (Add (Int i1,Int i2))
- deg (simplify (Add (p1,p2))) <= deg (Add (p1,p2))

The general statement can be made that for the case of p = Add(p1,p2):

deg (simplify (Add (p1,p2))) <= deg (Add (p1,p2))

##### For the case of p = Mul (p1,p2):
Our assumption becomes: <br>
deg (simplify (Mul (p1,p2))) <= deg (Mul (p1,p2))

Simplifying this, we find: <br>
deg (simplify (Mul (p1,p2))) = deg (simp_mul (simplify p1,simplify p2)) (evaluate simplify)

###### Then, for the sub-case that (simplify p1,simplify p2) = (Int 0,_)
deg (simplify (Mul (Int 0,_))) = deg (simplify (Int 0)) (evaluate simp_mul)

= deg (Int 0) (evaluate simplify)

= 0 (evaluate deg)

note that also: <br>
deg (Mul (Int 0,_)) = (deg (Int 0)) + (deg _)

= 0 + (deg _)

since 0 <= 0 + (deg _)

we can say that <br>
deg (simplify (Mul (Int 0,_)) <= deg (Mul (Int 0, _))

###### Then, for the sub-case that (simplify p1,simplify p2) = (_,Int 0)
deg (simplify (Mul (_,Int 0))) = deg (simplify (Int 0)) (evaluate simp_mul)

= deg (Int 0) (evaluate simplify)

= 0 (evaluate deg)

note that also: <br>
deg (Mul (_,Int 0)) = (deg _) + (deg (Int 0))

= (deg _) + 0

since 0 <= (deg _) + 0

we can say that <br>
deg (simplify (Mul (_,Int 0)) <= deg (Mul (_,Int 0))

###### Then, for the sub-case that (simplify p1,simplify p2) = (Int 1,p)
deg (simplify Mul (Int 1,p)) = deg p (evaluate simp_mul)

note that also, deg (Mul (Int 1,p)) = deg (Int 1) + deg p (evaluate deg)

= deg p (evaluate deg)

Thus, we can say that: <br>
deg (simplify Mul (Int 1,p)) = deg (Mul (Int 1,p))

###### Then, for the sub-case that (simplify p1,simplify p2) = (p,Int 1)
deg (simplify Mul (p,Int 1)) = deg p

note that also: <br> 
deg (Mul (p,Int 1)) = deg p (evaluate deg) + deg (Int 1)

= deg p (evaluate deg)

Thus, we can say that: <br>
deg (simplify Mul (p,Int 1)) = deg (Mul (p,Int 1))

###### Then, for the sub-case that (simplify p1,simplify p2) = (Int i1,Int i2)
deg (simplify (Mul (Int i1,Int i2))) = deg (Int (i1*i2)) (evaluate simp_mul)

= 0 (evaluate deg)

note that also: <br>
deg ( Mul (Int i1,Int i2)) = deg (Int i1) + deg (Int i2) (evaluate deg)

= 0 + 0 (evaluate deg)

Thus, we can say that: <br>
deg (simplify (Mul (Int i1,Int i2))) = deg ( Mul (Int i1,Int i2))

###### Then, for the sub-case that (simplify p1,simplify p2) = (simplify p1,simplify p2)
deg (Mul (simplify p1,simplify p2)) = deg (simplify p1) + deg (simplify p2) (evaluate deg)

note that also: <br>
deg (Mul (p1,p2)) = (deg p1) + (deg p2) (evaluate deg)
And that, by our assumption, <br>
deg (simplify p1) <= deg p1 (evaluate deg)
and <br>
deg (simplify p2) <= deg p2 (evaluate deg)

Thus we can say that: <br>
deg (simplify p1) + deg (simplify p2) <= (deg p1) + (deg p2)

and consequentially: <br>
deg (Mul (simplify p1,simplify p2)) <= deg (Mul (p1,p2))

###### Generalizing all of these sub-cases:
Since we now know that: <br>
deg (simplify (Mul (Int 0,_)) <= deg (Mul (Int 0, _)) <br>
and that: <br>
deg (simplify (Mul (_,Int 0)) <= deg (Mul (_,Int 0)) <br>
and that: <br>
deg (simplify Mul (Int 1,p)) = deg (Mul (Int 1,p)) <br>
and that: <br>
deg (simplify Mul (p,Int 1)) = deg (Mul (p,Int 1)) <br>
and that: <br>
deg (simplify (Mul (Int i1,Int i2))) = deg ( Mul (Int i1,Int i2)) <br>
and that: <br>
deg (Mul (simplify p1,simplify p2)) <= deg (Mul (p1,p2)) <br>

We can make the general statement that: <br>
deg (simplify (Mul (p1,p2))) <= deg (Mul (p1,p2))

##### Conclusion
Since we have shown that: <br>
deg (simplify (Add (p1,p2))) <= deg (Add (p1,p2)) <br>
And that: <br>
deg (simplify (Mul (p1,p2))) <= deg (Mul (p1,p2)) <br>

We can make the general statement that: <br>
&forall; p &isin; polyExpr: deg (simplify p) <= deg p

w<sup>5</sup>
