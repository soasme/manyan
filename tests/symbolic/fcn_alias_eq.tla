---- MODULE fcn_alias_eq ----
\* Regression for #29: aliased symbolic keys in fcn_eq, INF_FCNSET sv_pick/sv_enum, and guarded [{} -> {}].
EXTENDS TLC, FiniteSets, Integers
VARIABLES
  \* @type: Bool;
  b,
  \* @type: Bool;
  c,
  \* @type: Bool;
  d,
  \* @type: Int;
  x,
  \* @type: Int;
  y,
  \* @type: Int -> Int;
  f
Init == /\ b \in BOOLEAN /\ c \in BOOLEAN /\ d \in BOOLEAN
        /\ x \in {1, 2} /\ y \in {1, 2} /\ x = y
        /\ f \in [{x, y} -> {10, 20}]
Next == UNCHANGED <<b, c, d, x, y, f>>
Inv == /\ (IF c THEN (x :> 10) ELSE (y :> 10)) = (IF d THEN (x :> 10) ELSE (y :> 10))
       /\ ((f[x] = 10) => (f = (x :> 10)))
       /\ Cardinality([{x, y} -> {10, 20}]) = 2
       /\ ((~b) => Cardinality([(IF b THEN {1} ELSE {}) -> ({1} \ {1})]) = 1)
====
INIT Init
NEXT Next
INVARIANT Inv
