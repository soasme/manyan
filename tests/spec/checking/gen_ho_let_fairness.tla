---- MODULE gen_ho_let_fairness ----
\* Regression for #36: higher-order action params, LET UNCHANGED, LET action params, LET INSTANCE HO arg, IF WF.
EXTENDS Naturals
VARIABLES x, y
Apply(Op(_), v) == Op(v)
SetX(v) == x' = v
Step(a) == LET B == a IN B
F(p) == LET M == INSTANCE Helper WITH c <- p IN Apply(M!Add, 5)
Init == x = F(3) /\ y = 0
Next == \/ (x = 8 /\ Apply(SetX, 1) /\ LET vars == <<y>> IN UNCHANGED vars)
        \/ (x = 1 /\ Step(x' = 2) /\ LET vars == <<y>> IN UNCHANGED vars)
        \/ (x = 2 /\ UNCHANGED <<x, y>>)
Spec == Init /\ [][Next]_<<x, y>> /\ (IF TRUE THEN WF_<<x, y>>(Next) ELSE TRUE)
Prop == <>(x = 2)
====
SPECIFICATION Spec
PROPERTY Prop
