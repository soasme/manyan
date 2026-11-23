---- MODULE enabled_primed ----
\* ENABLED A is a state predicate whatever the level of A, so A may be an
\* action though ENABLED A is primed, as in Specifying Systems' RTBound.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Done(A) == ~(ENABLED A)'
Prop == [][Done(Next) <=> x' = 2]_x
====
INIT Init
NEXT Next
PROPERTY Prop
CHECK_DEADLOCK FALSE
