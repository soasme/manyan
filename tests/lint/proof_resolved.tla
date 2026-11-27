---- MODULE proof_resolved ----
\* What a proof names, resolved as SANY: steps, DEFINE, TAKE, PICK and
\* NEW in scope where they are, labels in steps, @ of the step before.
EXTENDS Naturals
F(a) == a + 1
THEOREM T == ASSUME NEW n \in Nat PROVE F(n) > n
  <1> DEFINE G == F(n)
  <1>1. G = n + 1
    BY DEF G, F
  <1>2. @ > n
    OBVIOUS
  <1>3. ASSUME NEW m \in Nat PROVE lab :: m + G > n
    BY <1>1
  <1> TAKE k \in Nat
  <1> PICK j \in Nat : j = k
  <1> QED BY <1>1, <1>2, T DEF G
THEOREM TRUE BY T
====
