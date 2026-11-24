\* options: -length 5
---- MODULE lasso_late_loop ----
\* Regression for #27: sym_loop must allow loops starting after state 0 even when st[k] = st[0].
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x = 0
Next == x' \in {0, 1}
Prop == (<>(x = 1)) => ([]<>(x = 1))
====
INIT Init
NEXT Next
PROPERTY Prop
