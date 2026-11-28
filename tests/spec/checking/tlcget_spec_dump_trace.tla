---- MODULE tlcget_spec_dump_trace ----
\* TLCGet("spec")'s fields as TLC interned them: -dumpTrace json's module
\* names "actions" first, tla's IOUtils "parameters".
\* options: -continue -dumpTrace json trace.json -dumpTrace tla trace.tla
EXTENDS TLC, Naturals
CONSTANT P
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A(p) == x < 2 /\ x' = x + p /\ UNCHANGED y
B == y < 1 /\ y' = y + 1 /\ UNCHANGED x
Next == (\E p \in P : A(p)) \/ B
Spec == Init /\ y = y /\ [][Next]_vars /\ WF_vars(B) /\ SF_vars(Next)
TypeOK == x \in Nat /\ y \in Nat
Small == x < 10
Ini == x = 0
Box == [][x' >= x]_vars
Ev == <>(y = 1)
Prop == Ini /\ Box /\ Ev /\ []Small /\ [](y >= 0)
Con == x < 5
ACon == x' < 5
ASSUME PrintT(TLCGet("spec"))
====
CONSTANT P = {1, 2}
SPECIFICATION Spec
INVARIANT TypeOK Small
PROPERTY Prop
CONSTRAINT Con
ACTION_CONSTRAINT ACon
CHECK_DEADLOCK FALSE
