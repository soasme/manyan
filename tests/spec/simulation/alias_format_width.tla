---- MODULE alias_format_width ----
\* options: -simulate num=1 -depth 5 -seed 1
\* An ALIAS _format too wide for Java's heap, met as a simulation prints its
\* behavior: TLC's worker reports that it ran out of memory.
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = 1
Inv == x = 0
Alias == [x |-> x, _format |-> "%2147483647s"]
====
INIT Init
NEXT Next
INVARIANT Inv
ALIAS Alias
