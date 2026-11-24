---- MODULE except_at_scoping ----
\* Regression for #33: @ in EXCEPT must be lexically scoped across LET and lazy filters.
VARIABLE x, y
Init == /\ x = [[a |-> 10] EXCEPT !.a = LET old == @ IN [[b |-> 20] EXCEPT !.b = old]]
        /\ y = [[a |-> {1}] EXCEPT !.a = {s \in SUBSET {1, 2} : s = @}]
Next == UNCHANGED <<x, y>>
Inv == x.a.b = 10 /\ ({1} \in y.a) /\ ~({2} \in y.a)
====
INIT Init
NEXT Next
INVARIANT Inv
