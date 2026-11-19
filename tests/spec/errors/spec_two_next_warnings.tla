---- MODULE spec_two_next_warnings ----
\* Two conjuncts [][Next]_v: TLC warns of each subscript's missing
\* variables before it reports there are two.
EXTENDS Naturals
VARIABLES z, w
Spec == z = 0 /\ [][z' = z + 1]_z /\ w = 0 /\ [][UNCHANGED w]_w
====
SPECIFICATION Spec
