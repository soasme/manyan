---- MODULE lazy_empty_and_lambda ----
\* Regression for #34: [{} -> Nat], {} \X Nat, Cardinality with empty factor, EXCEPT on V_LAMBDA, Append(s, Nat).
EXTENDS Naturals, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == /\ Cardinality([{} -> Nat]) = 1
       /\ [{} -> Nat] = {<<>>}
       /\ ({} \X Nat) = {}
       /\ Cardinality((1..100000) \X (1..100000) \X {}) = 0
       /\ [[i \in Nat |-> i] EXCEPT ![-1] = 42][5] = 5
       /\ [[s \in SUBSET {1, 2} |-> 0] EXCEPT ![{3}] = 1][{1}] = 0
       /\ Len(Append(<<1>>, Nat)) = 2
====
INIT Init
NEXT Next
INVARIANT Inv
