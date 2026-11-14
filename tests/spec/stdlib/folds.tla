---- MODULE folds ----
\* CommunityModules' folds and searches of sequences, which TLC computes in
\* Java: FoldFunction applies op(f[k], acc) in the order of the domain,
\* FoldBag op(acc, e) for each copy of e. Found by etcd's trace validation.
EXTENDS Naturals, Sequences, SequencesExt, Functions, BagsExt, TLC
s == <<3, 1, 4, 1, 5, 9, 2, 6>>
ASSUME PrintT(FoldSeq(LAMBDA x, y: <<x>> \o y, <<>>, s))
ASSUME PrintT(FoldFunction(LAMBDA x, y: x + 2 * y, 0, [a |-> 1, b |-> 2, c |-> 3]))
ASSUME PrintT(FoldFunctionOnSet(LAMBDA x, y: <<x>> \o y, <<>>, s, {2, 5, 7}))
ASSUME PrintT(FoldBag(LAMBDA x, y: x \o <<y>>, <<>>, [a |-> 2, b |-> 1]))
ASSUME PrintT(<<SelectInSeq(s, LAMBDA x: x = 1), SelectLastInSeq(s, LAMBDA x: x = 1), SelectInSeq(s, LAMBDA x: x > 9)>>)
ASSUME PrintT(<<SelectInSubSeq(s, 3, 7, LAMBDA x: x = 1), SelectLastInSubSeq(s, 1, 3, LAMBDA x: x = 1),
                SelectInSubSeq(s, 5, 2, LAMBDA x: TRUE)>>)
ASSUME PrintT(<<IsPrefix(<<3, 1>>, s), IsPrefix(<<3, 2>>, s), IsPrefix(s, <<3>>), IsPrefix("ab", "abc"), IsPrefix(<<>>, <<>>)>>)
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
