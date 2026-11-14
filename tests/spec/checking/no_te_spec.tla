---- MODULE no_te_spec ----
\* -noGenerateSpecTE: TLC sets up no trace spec, which would have interned
\* "state" first: CounterExample's action comes first. TLC reads Integers
\* as it reports the error, so Naturals' operators are Integers' in Java.
\* options: -noGenerateSpecTE
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
Post == PrintT(CounterExample) /\ PrintT(1 + TRUE)
====
INIT Init
NEXT Next
INVARIANT Inv
POSTCONDITION Post
