---- MODULE eval_in_next_continue ----
\* options: -deadlock -continue
\* An error in an operator of Naturals as the next state is computed,
\* reported twice with -continue: TLC exits as for a standard module's.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 10 \div (2 - x)
====
INIT Init
NEXT Next
