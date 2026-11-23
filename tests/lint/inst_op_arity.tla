---- MODULE inst_op_arity ----
---- MODULE Inner ----
CONSTANT F(_)
Op == F(1)
====
G(x, y) == x
INSTANCE Inner WITH F <- G
====
