---- MODULE label_wrong_arity ----
A == \A x \in {1} : L(x) :: x = 1
B == A!L(1, 2)
====
