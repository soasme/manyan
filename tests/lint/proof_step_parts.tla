---- MODULE proof_step_parts ----
\* A step that is not an assertion has parts, as SANY: CASE, HAVE and
\* WITNESS what they list, PICK x \in S : e those of \E x \in S : e, TAKE
\* its sets. A USE step has none, and is neither an expression nor a fact.
THEOREM TRUE
<1>1. CASE 1 = 1
<1>2. WITNESS 1, 2
<1>3. PICK a \in {1} : lab(a) :: a = 1
<1>4. TAKE b \in {2}
<1>5. <1>1!1!1 = <1>2!2 /\ <1>3!1 = <1>4!1 /\ <1>3!lab(1)
<1>6. USE <1>1, <1>3
<1> QED BY <1>6
====
