---- MODULE alias_after_error_continue ----
\* options: -simulate num=2 -depth 5 -seed 1 -continue
\* A simulation going on after an error keeps no behavior for its
\* CounterExample, so TLC does not evaluate the ALIAS on it again.
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x < 4 /\ x' = x + 1
Inv == x # 2
Alias == [y |-> x, p |-> PrintT(<<"alias", x>>)]
Post == PrintT(<<"post", CounterExample.state>>)
====
INIT Init
NEXT Next
INVARIANT Inv
ALIAS Alias
POSTCONDITION Post
