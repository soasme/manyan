---- MODULE unify_var_cycle ----
\* Regression for #21: TY_VAR vs TY_VAR cycle must fail cleanly, not stack overflow.
F(r, l, x) == r = {l} /\ l = {x} /\ r = l
====
