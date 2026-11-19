---- MODULE tlcget_registers ----
\* Numbered and named ("s:") registers, and TLCGet("all") and "all:named":
\* each register to the tuple of its value in each worker, which in Manyan
\* is one. TLCGetOrDefault reads a named one too.
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
ASSUME TLCSet(6, "a") /\ TLCSet(1, 5) /\ TLCSet("s:b", 1) /\ TLCSet("s:a", {2})
ASSUME PrintT(TLCGet("all")) /\ PrintT(TLCGet("all:named"))
ASSUME PrintT(<<TLCGetOrDefault("s:a", 0), TLCGetOrDefault("s:c", 0), TLCGetOrDefault("c", 0)>>)
Init == x = 0
Next == x < 2 /\ x' = x + 1 /\ TLCSet(1, x) /\ TLCSet("s:b", x')
Inv == PrintT(<<TLCGet("all"), TLCGet("all:named"), TLCGet("s:b")>>)
====
INIT Init
NEXT Next
INVARIANT Inv
CHECK_DEADLOCK FALSE
