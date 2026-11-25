---- MODULE nested_leadsto ----
\* Nested leads-to on the left (both ~> FALSE and ~> state predicate) must
\* build a compact tableau without exponential blowup.
\* options: -deadlock
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Spec == Init /\ [][Next]_x
Prop == ((((((((x = 1) ~> (x = 2)) ~> FALSE) ~> FALSE) ~> FALSE) ~> FALSE)
          ~> FALSE) ~> FALSE) ~> FALSE
====
SPECIFICATION Spec
PROPERTY Prop
