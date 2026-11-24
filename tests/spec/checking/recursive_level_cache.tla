---- MODULE recursive_level_cache ----
\* Regression for #25: forward RECURSIVE inside [] must not cache level 0.
EXTENDS Naturals
VARIABLE x
RECURSIVE F(_)
Prop == []F(0)
F(n) == IF n = 0 THEN x = 0 ELSE F(n - 1)
Wrap == L :: F(0)
Inv == Wrap!L
Init == F(0)
Next == x' = 1
====
INIT Init
NEXT Next
INVARIANT Inv
