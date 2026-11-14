---- MODULE inv_option_syntax ----
\* An -inv that does not parse is TLC's parse error.
\* options: -inv "x <"
VARIABLE x
Init == x = 0
Next == x' = x
====
INIT Init
NEXT Next
