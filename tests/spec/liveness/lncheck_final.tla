---- MODULE lncheck_final ----
\* TLC's -lncheck final checks liveness once the state graph is done, as
\* manyan always does; -teSpecOutDir and -noGenerateSpecTE are for the
\* trace spec manyan never writes.
\* options: -lncheck final -teSpecOutDir te -noGenerateSpecTE
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
Live == <>(x = 2)
====
SPECIFICATION Spec
PROPERTY Live
