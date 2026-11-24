---- MODULE recursive_subexpr_label ----
\* Regression for #16: subexpression label selector on forward RECURSIVE.
RECURSIVE F(_)
G == F(1)!lab(2)
F(x) == \A y \in {1, 2} : lab(y) :: x = y
====
