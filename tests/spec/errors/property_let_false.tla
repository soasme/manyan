---- MODULE property_let_false ----
\* TLC takes a property apart before it checks it, a LET by its body: one
\* that is FALSE makes the spec trivially false, though the LET's
\* definitions use a variable.
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
Prop == LET y == x IN FALSE
====
SPECIFICATION Spec
PROPERTY Prop
