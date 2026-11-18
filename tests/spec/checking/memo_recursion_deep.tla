---- MODULE memo_recursion_deep ----
\* Calls kept as a recursion returns, more than the table had room for when
\* it began: Sum keeps 511, half the table, then Twice keeps 521 more.
EXTENDS Naturals
RECURSIVE Sum(_), Twice(_)
Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)
Twice(n) == IF n = 0 THEN 0 ELSE 2 + Twice(n - 1)
ASSUME Sum(510) = 130305
ASSUME Twice(520) = 1040
====
