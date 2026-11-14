---- MODULE inv_option_operator ----
\* -inv naming an operator of the root checks it under its own name.
\* options: -inv Small
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Small == x < 3
====
INIT Init
NEXT Next
