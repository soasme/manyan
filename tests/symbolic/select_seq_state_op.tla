---- MODULE select_seq_state_op ----
\* Regression for #39: SelectSeq with named state-reading operator in -symbolic.
EXTENDS Sequences, Integers
VARIABLE
  \* @type: Int;
  x
Pred(e) == e > x
Init == x = 1
Next == UNCHANGED x
Inv == SelectSeq(<<1, 2, 3>>, Pred) = <<2, 3>>
====
INIT Init
NEXT Next
INVARIANT Inv
