---- MODULE dump_error_stuttering ----
\* Next fails on x = 0 with a temporal property: TLC expands the state
\* again to report the error, and -dump writes its stuttering step.
\* options: -dump states
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = CHOOSE v \in {1} : v > x + 5
Spec == Init /\ [][Next]_x
P == <>[](x \in 1)
====
SPECIFICATION Spec
PROPERTY P
