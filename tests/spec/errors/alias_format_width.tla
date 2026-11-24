---- MODULE alias_format_width ----
\* Regression for #12: large width in ALIAS _format must not overflow or crash.
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
