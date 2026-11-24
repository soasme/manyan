---- MODULE let_enabled_level ----
\* Regression for #37: X_LET level is body level, not max over local definitions.
VARIABLE x
Init == x = 0
Next == x' = x
Prop == [](LET A == x' = x IN ENABLED A)
====
INIT Init
NEXT Next
PROPERTY Prop
