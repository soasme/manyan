\* options: -deadlock
---- MODULE stutter_loop_replay ----
\* Regression for #31: stuttering liveness counterexample at depth >= 1 must set loop = n - 1.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
A == x = 0 /\ x' = 1
B == x = 1 /\ x' = 2
Init == x = 0
Next == A \/ B
Spec == Init /\ [][Next]_x /\ WF_x(A)
Prop == []<>(x = 0)
====
SPECIFICATION Spec
PROPERTY Prop
