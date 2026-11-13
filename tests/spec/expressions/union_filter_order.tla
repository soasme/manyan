---- MODULE union_filter_order ----
\* A filter of a UNION TLC keeps tests the elements of each set in turn,
\* duplicates too, not the UNION sorted: SA, the smaller set, comes first
\* but holds the larger values. Init takes k = 2 and fails at k = 5 before
\* the test is undefined at k = 1.
EXTENDS Integers, TLC
SA == [{"k"} -> {2, 5}]
SB == [{"k"} -> {1, 2, 3}]
ASSUME PrintT({f \in UNION {SA, SB} : PrintT(f.k)})
VARIABLE x
Init == x \in {f \in UNION {SA, SB} : 10 \div (f.k - 1) > 0}
Next == x' = x
Inv == x.k < 5
====
INIT Init
NEXT Next
INVARIANT Inv
