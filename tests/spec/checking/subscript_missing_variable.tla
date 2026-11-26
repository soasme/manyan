---- MODULE subscript_missing_variable ----
\* semantics: [Next]_vars lets a and b change, which TLC does not explore
\* The subscript of the specification's next-state relation leaves out
\* variables: TLC warns of each, looking through tuples, definitions and
\* their arguments, then explores Next alone; Manyan stops.
EXTENDS Naturals
VARIABLES zed, a, mm, b
Init == zed = 0 /\ a = 0 /\ mm = 0 /\ b = 0
Next == zed' = 1 /\ UNCHANGED <<a, mm, b>>
W(v) == <<v, <<mm>>>>
vars == W(zed)
Spec == Init /\ [][Next]_vars
====
SPECIFICATION Spec
