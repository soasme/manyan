Preamble text before the module is preserved.

---- MODULE comments ----
(* Module header comment
   (* nested block comment *)
   stays intact. *)
EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Set(Int);
    S

VARIABLE x  \* state counter

Init == (* Global variables *)
    /\ x = 0  \* initial value
    \* keep x in bounds
    /\ x \in S

Next ==
    /\ x' = [f \in {1, 2} |->
            IF f = 1 THEN x + 1 ELSE x]  \* trailing comment
    /\ [a |-> 1,
        \* field b
        b |-> 2].a = 1
====
Postscript after module is preserved.
