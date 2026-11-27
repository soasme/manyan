---- MODULE recursive_arity_where ----
\* A definition of another arity than its RECURSIVE declaration is an
\* error where it is, after the errors before it.
A == LET RECURSIVE F(_)
         G == foo
         F(a, b) == 1 IN 1
====
