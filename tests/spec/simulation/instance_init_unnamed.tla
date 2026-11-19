---- MODULE instance_init_unnamed ----
\* An initial predicate seen through an instance that substitutes is
\* unnamed: TLC labels its states "Initial predicate", and TLCGet("action")
\* and TLCGet("spec") name it UnnamedAction.
\* options: -simulate -depth 5 -seed 1
EXTENDS TLC, Naturals
VARIABLE x
I == INSTANCE Inner WITH z <- x
Spec == I!ISpec
Inv == x < 1
ASSUME PrintT(TLCGet("spec").inits)
====
SPECIFICATION Spec
INVARIANT Inv
