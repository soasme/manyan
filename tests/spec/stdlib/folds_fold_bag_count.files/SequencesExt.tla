---- MODULE SequencesExt ----
\* CommunityModules' operators the test uses, with their definitions: TLC
\* replaces them by its Java, as Manyan by its own.
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE Functions
FoldSeq(op(_, _), base, seq) == FoldFunction(op, base, seq)
SelectInSeq(seq, Test(_)) == CHOOSE i \in 0..Len(seq) : TRUE
SelectInSubSeq(seq, from, to, Test(_)) == CHOOSE i \in 0..Len(seq) : TRUE
SelectLastInSeq(seq, Test(_)) == CHOOSE i \in 0..Len(seq) : TRUE
SelectLastInSubSeq(seq, from, to, Test(_)) == CHOOSE i \in 0..Len(seq) : TRUE
IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))
====
