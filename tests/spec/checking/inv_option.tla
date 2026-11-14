---- MODULE inv_option ----
\* -inv adds an expression as an invariant, after the configuration's: TLC
\* names it __DebuggerExpr__ and the time; each -inv is one more.
\* options: -inv "x < 2" -inv "y = \"a\""
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = "a"
Next == x' = (x + 1) % 5 /\ y' = IF x = 0 THEN "b" ELSE "a"
Inv == x < 4
====
INIT Init
NEXT Next
INVARIANT Inv
