---- MODULE let_inst_symbolic ----
\* Regression for #21: LET containing local INSTANCE must not NULL-deref in let_ctx.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x = 1
Next == x' = x
Inv == LET N == INSTANCE Naturals IN N!+(x, 1) = 2
====
INIT Init
NEXT Next
INVARIANT Inv
