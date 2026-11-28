---- MODULE view_tuple_names ----
\* -view prints a VIEW's tuple as long as the constants and variables it
\* uses as `/\ name = value` lines, as TLC: its values in turn, paired with
\* them in the order of the state, a constant first; of two constants,
\* TLC keeps the first declared. The names need not be the values'.
\* options: -view
EXTENDS Naturals
CONSTANT L, K
VARIABLE y, x
Init == x = 0 /\ y = 0
Next == x < 3 /\ x' = x + 1 /\ y' = y + 2
V == <<K, L, x + y, y>>
Inv == x < 2
====
CONSTANT K = 5 L = 6
INIT Init
NEXT Next
VIEW V
INVARIANT Inv
