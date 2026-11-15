---- MODULE tlcfp ----
\* TLCFP is TLC's fingerprint of a value under the -fp polynomial: equal
\* values of any form agree; a model value of the configuration is
\* fingerprinted by its index in TLC's table of names.
\* options: -fp 7
EXTENDS Integers, Sequences, TLC, TLCExt
CONSTANT m1, m2, s
Vals == <<TRUE, FALSE, 0, -1, 2147483647, "", "ab", "héllo", {}, {3, 1, 2}, 1..3, 3..2,
          <<>>, <<"a", TRUE>>, [a |-> 1, b |-> 2], [i \in 1..3 |-> i * i], (1 :> 2) @@ (5 :> 3),
          SUBSET {1, 2}, [{1, 2} -> {"u"}], {1, 2} \X {"z"}, m1, {m1, m2}, [x |-> m2], s>>
ASSUME \A i \in 1..Len(Vals) : PrintT(TLCFP(Vals[i]))
ASSUME TLCFP(1..3) = TLCFP({1, 2, 3}) /\ TLCFP(<<4, 5>>) = TLCFP([i \in 1..2 |-> i + 3])
====
CONSTANT s = "str"
CONSTANT m2 = m2
CONSTANT m1 = m1
