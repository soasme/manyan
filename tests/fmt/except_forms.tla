---- MODULE except_forms ----
EXTENDS Naturals
VARIABLE f, r

Flat == [f EXCEPT ![1] = @ + 1]
Chained == [r EXCEPT !.a[1].b[2] = @ + 1, !.c = 0]
MultiIndex == [f EXCEPT ![1, 2] = 3]
Nested == [f EXCEPT ![1] = [@ EXCEPT ![2] = @ + 1]]
KeywordField == [r EXCEPT !.IF = 1].CASE
====
