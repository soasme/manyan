---- MODULE dump_simulate ----
\* TLC makes the -dump file as it starts, simulating too, and writes no
\* state to it: the dot graph's head, unclosed.
\* options: -simulate num=2 -depth 3 -dump dot states
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
INIT Init
NEXT Next
