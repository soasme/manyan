---- MODULE brace_in_precedence ----
\* semantics: {y \in S /\ P} is {(y \in S) /\ P}, which SANY parses as {y \in (S /\ P)}
\* Without a colon, SANY reads {y \in ...} with the rest as the right side
\* of \in, unchecked for precedence; TLA+'s precedence binds \in tighter.
EXTENDS Naturals, TLC
Op(y) == {y \in {1} /\ y = 3}
ASSUME PrintT(Op(1))
====
