---- MODULE synonyms ----
EXTENDS Naturals, Sequences, Bags
CONSTANTS C
VARIABLES x
Op ==
    /\ \forall a \in {1, 2} : \exists b \in {1, 2} :
           (a <= b \land b =< a \lor a >= b) \equiv (a # b)
    /\ \lnot \neg (1 \in ({1} \union {2}) \intersect {1})
    /\ ({1} \times {2}) = ({1} \X {2})
    /\ (<<1>> \circ <<2>>) = (<<1>> \o <<2>>)
    /\ (EmptyBag (+) EmptyBag) = (EmptyBag (-) EmptyBag)
====
