---- MODULE higher_order_inst_level ----
\* Regression for #25: higher-order CONSTANT F(_) substitution level in INSTANCE.
---- MODULE M ----
CONSTANT F(_)
Op == F(0)
====
VARIABLE x
G(n) == x = n
I == INSTANCE M WITH F <- G
Wrap == L :: I!Op
Inv == Wrap!L
Init == I!Op
Next == x' = 1
====
INIT Init
NEXT Next
INVARIANT Inv
