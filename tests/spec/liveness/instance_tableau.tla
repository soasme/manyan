---- MODULE instance_tableau ----
\* Regression for #24: tnode_add must distinguish atoms from distinct INSTANCEs.
VARIABLES x, y
I1 == INSTANCE SubM WITH v <- x
I2 == INSTANCE SubM WITH v <- y
Init == x = 1 /\ y = 0
Next == UNCHANGED <<x, y>>
Prop == I1!AlwaysOne => I2!AlwaysOne
====
INIT Init
NEXT Next
PROPERTY Prop
