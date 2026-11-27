---- MODULE fcn_subexpression ----
\* A part of a function definition, as of the constructor it is: f!1 its
\* domain, f!(3) its value at 3, labels and parts of a recursive one.
EXTENDS TLC, Naturals
f[a \in 1..3] == a * 10
g[a \in 1..2, b \in {5}] == lab(a, b) :: <<a, b>>
h[n \in Nat] == IF n = 0 THEN 0 ELSE n + h[n - 1]
ASSUME PrintT(<<f!(3), f!1, g!(1, 5), g!lab(1, 5), g!2, h!(2)!1, h!(0)!2>>)
====
