---- MODULE property_box_parameter ----
\* []x, x a parameter, is named x, whatever its argument.
VARIABLE b
R(x) == []x
Init == b = FALSE
Next == b' = b
Spec == Init /\ [][Next]_b
P == R(b)
====
SPECIFICATION Spec
PROPERTY P
