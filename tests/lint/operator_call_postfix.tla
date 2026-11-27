---- MODULE operator_call_postfix ----
\* An operator applied as a name, '(e) or +(a, b), takes postfixes as any
\* operand, and is no postfix of ENABLED's operand.
EXTENDS Naturals
VARIABLE x
P == ENABLED '(x)[1] /\ +(1, 2)' = 3 /\ ENABLED '(x = 1)
====
