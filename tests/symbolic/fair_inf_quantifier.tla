\* options: -length 2
---- MODULE fair_inf_quantifier ----
\* Regression for #39: fair action quantifying over infinite set Nat in -symbolic.
EXTENDS Naturals
VARIABLE
  \* @type: Int;
  x
A == \E n \in Nat : n > x /\ x' = n
Init == x = 0
Next == A
Spec == Init /\ [][Next]_x /\ WF_x(A)
Prop == <>(x > 0)
====
SPECIFICATION Spec
PROPERTY Prop
