---- MODULE tlcget_spec_instance ----
\* TLCGet("spec") of a specification seen through an instance that
\* substitutes: its parts are unnamed, located by the instance; and of an
\* unnamed next-state action, in an invariant.
EXTENDS TLC, Naturals
VARIABLE x
I == INSTANCE Inner WITH z <- x
Spec == I!ISpec
P == I!ISpec
ASSUME PrintT(TLCGet("spec"))
Inv == x = 0 \/ PrintT(TLCGet("spec").actions)
====
SPECIFICATION Spec
PROPERTY P
INVARIANT Inv
CHECK_DEADLOCK FALSE
