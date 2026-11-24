---- MODULE arg_pure_except_key ----
\* Regression for #35: arg_pure must not treat EXCEPT keys with side effects as pure.
EXTENDS TLC
VARIABLE x
F(a, b) == CHOOSE y \in {a} : TRUE
Init == TLCSet(1, 0) /\ x = F(5, [<<1>> EXCEPT ![IF TLCSet(1, 99) THEN 1 ELSE 1] = 2])
Next == x' = x
Inv == TLCGet(1) = 0
====
INIT Init
NEXT Next
INVARIANT Inv
