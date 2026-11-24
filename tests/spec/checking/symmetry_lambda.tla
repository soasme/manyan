---- MODULE symmetry_lambda ----
\* Regression for #23: SYMMETRY must permute V_LAMBDA functions.
EXTENDS TLC
CONSTANT M
VARIABLES m, f
Sym == Permutations(M)
Init == m \in M /\ f = [s \in SUBSET M |-> m \in s]
Next == m' \in M /\ UNCHANGED f
Inv == f[{m}] = TRUE
====
CONSTANT M = {m1, m2}
SYMMETRY Sym
INIT Init
NEXT Next
INVARIANT Inv
