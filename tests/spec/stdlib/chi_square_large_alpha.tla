---- MODULE chi_square_large_alpha ----
\* Regression for #20: non-finite alpha in ChiSquare must not trigger java_number NULL UB.
EXTENDS Statistics
VARIABLE x
Init == x = ChiSquare(<<1, 1>>, <<1, 1>>, "Infinity")
Next == x' = x
====
INIT Init
NEXT Next
