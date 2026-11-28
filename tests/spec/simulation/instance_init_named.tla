---- MODULE instance_init_named ----
\* An instance's initial predicate the specification calls whole is named
\* by it, I!Init, though a conjunction and though the instance renames a
\* variable; seen through the instance's specification it is unnamed
\* (instance_init_unnamed).
\* options: -simulate -depth 5 -seed 1
EXTENDS TLC, Naturals
VARIABLE u, w
I == INSTANCE Pair WITH v <- u
Spec == I!Init /\ [][I!Next]_<<u, w>>
Inv == u < 3
ASSUME PrintT(TLCGet("spec").inits)
====
SPECIFICATION Spec
INVARIANT Inv
