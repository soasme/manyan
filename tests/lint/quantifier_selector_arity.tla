---- MODULE quantifier_selector_arity ----
\* !(...) of a quantifier gives a value to each name it binds.
F == \A a, b : a = b
P == F!(1)
====
