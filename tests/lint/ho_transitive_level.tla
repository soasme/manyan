---- MODULE ho_transitive_level ----
VARIABLE x
Prime(a) == a'
B(P(_)) == P(x')
A(Op(_)) == B(Op)
Bad == A(Prime)
====
