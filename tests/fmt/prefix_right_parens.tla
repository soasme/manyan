---- MODULE prefix_right_parens ----
\* Regression for #38: right-hand prefix op under non-left-assoc infix op needs parens.
a ^ b == a \cup b
a + b == a \ b
Op(A, B, C) == (A ^ (UNION B)) + C
====
