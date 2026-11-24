---- MODULE stack_gen_let_rec ----
\* Regression for #19: LET RECURSIVE in generator must respect -stack.
\* options: -stack 20
VARIABLE x
Init == x = 0
Next == (x = 0) /\ LET RECURSIVE F(_) F(n) == FALSE \/ F(n) IN F(0)
====
INIT Init
NEXT Next
