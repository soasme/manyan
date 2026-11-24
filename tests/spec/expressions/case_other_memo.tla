---- MODULE case_other_memo ----
\* Regression for #17: CASE ... [] OTHER passed to a memoizable operator.
VARIABLE x
F(a) == CHOOSE y \in {a} : TRUE
Init == x = F(CASE FALSE -> 1 [] OTHER -> 2)
Next == x' = x
====
INIT Init
NEXT Next
