---- MODULE instance_lambda_action ----
\* A constant operator an instance substitutes with a LAMBDA, called in an
\* action with a primed argument: the LAMBDA's body assigns it, as TLC,
\* and sees the parameter of the instance's definition.
EXTENDS Naturals
VARIABLE v
I == INSTANCE Stepper WITH Step <- LAMBDA a, b : b = a + 1
J(k) == INSTANCE Stepper WITH Step <- LAMBDA a, b : b = a + k
Init == v = 0
Next == I!Next \/ J(2)!Next
====
INIT Init
NEXT Next
