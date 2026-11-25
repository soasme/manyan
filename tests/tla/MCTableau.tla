------------------------------ MODULE MCTableau -------------------------------
(* Formulas over the literals of p and q up to depth three, among them
   []<>p, <>[]p, [](p \/ <>q) and <>(p /\ []q), on every lasso of up to
   three states. *)
EXTENDS Tableau
L0 == {Lit(o) : o \in {"p", "~p", "q", "~q"}}
LC == {Lit(o) : o \in {"p", "~p", "true", "false"}}
U(S) == {[op |-> o, args |-> <<a>>] : o \in {"always", "eventually"}, a \in S}
B(S, T) == {[op |-> o, args |-> <<a, b>>] : o \in {"and", "or"}, a \in S, b \in T}
F1 == L0 \cup U(L0) \cup B(L0, L0)
FC == LC \cup U(LC) \cup B(LC, LC)
All == F1 \cup U(F1) \cup B(U(L0), U(L0)) \cup U(U(L0) \cup B(U(L0), L0)) \cup FC \cup U(FC) \cup B(U(LC), LC)
AllLassos == UNION {{[w |-> s, loop |-> k] : s \in [1..n -> SUBSET {"p", "q"}], k \in 1..n} : n \in 1..3}
================================================================================
CONSTANT Formulas <- All
CONSTANT Lassos <- AllLassos
SPECIFICATION Spec
INVARIANT Same
