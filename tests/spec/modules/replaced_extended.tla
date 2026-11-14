---- MODULE replaced_extended ----
\* TLC evaluates a definition again where a name it replaces calls it: at
\* startup, for the module defining the name and for each extending it,
\* and at each use. Called by its own name, it is computed once.
EXTENDS Log, TLC
B == PrintT("rootB")
Read == IF PrintT("read") THEN <<1, 2>> ELSE <<>>
Spec == Init /\ Len(Read) = 2 /\ Len(Read) = 2 /\ [][Next]_x
====
SPECIFICATION Spec
CONSTANT Entries <- Read
