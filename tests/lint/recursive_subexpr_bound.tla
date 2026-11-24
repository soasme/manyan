---- MODULE recursive_subexpr_bound ----
\* Regression for #16: subexpression binder selector on forward RECURSIVE.
RECURSIVE F(_)
G == F(1)!(2)
F(x) == \A y \in {1, 2} : x = y
====
