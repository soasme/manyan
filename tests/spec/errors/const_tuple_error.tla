---- MODULE const_tuple_error ----
\* A failed constant evaluation inside a function application must not leak
\* keep_lazy = 1 into the model check.
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x
P == "B" \notin DOMAIN [t \in {"A"} |-> <<1 \div 0>>[1]]
====
SPECIFICATION Spec
INVARIANT P
