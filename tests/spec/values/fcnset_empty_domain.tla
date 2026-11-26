---- MODULE fcnset_empty_domain ----
\* [{} -> T] is {<<>>} whatever T is: TLC enumerates it without T, as
\* Nat, Int, or a set it cannot enumerate. Found by lean/'s reference.
EXTENDS Integers, FiniteSets, TLC
ASSUME PrintT([{} -> Int])
ASSUME PrintT([{} -> {x \in Nat : FALSE}])
ASSUME PrintT([{} -> ({8} \cup Int)])
ASSUME PrintT(Cardinality([{} -> Nat \ {1}]))
ASSUME PrintT({f \in [{} -> Int] : TRUE})
ASSUME PrintT(<<>> \in [{} -> Int])
====
