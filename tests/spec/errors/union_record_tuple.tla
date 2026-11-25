---- MODULE union_record_tuple ----
\* Comparing a record with a non-record function (tuple or V_LAMBDA) in a set
\* union must fail with TLC's record comparison error even when lengths differ.
EXTENDS Integers, FiniteSets, TLC
ASSUME PrintT(Cardinality({[x \in 1..1 |-> -3]} \cup {[a |-> 5, b |-> FALSE]}))
====
