---- MODULE instance_action_parameters ----
\* An action through instances that substitute is labelled by the
\* parameters on the way, the instances' and then the definition's, as
\* TLC: J!A(2,0,1) for J(2, 0)!A(1). An argument that is not constant
\* makes the call one action, located there and unlabelled.
EXTENDS Naturals, TLC
VARIABLE v
J(k, m) == INSTANCE Steps WITH K <- k
J2 == INSTANCE Steps WITH K <- 0
Init == v = 0
Next == \/ J(2, 0)!A(1)
        \/ J(1, 7)!B
        \/ \E q \in {3} : J(q, 0)!A(q)
        \/ J2!A(4)
        \/ J(2, 0)!A(v % 2)
Inv == v # 6
ASSUME PrintT(TLCGet("spec").actions)
====
INIT Init
NEXT Next
INVARIANT Inv
