---- MODULE tlc_register_worker ----
\* Regression for #32: TLCSet/TLCGet registers must not be lost under -workers > 1.
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in 0..200
Next == (x = 100 => TLCSet(1, 42)) /\ x' = x
Post == TLCGet(1) = 42
====
INIT Init
NEXT Next
POSTCONDITION Post
