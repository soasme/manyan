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
FoldLeft(op(_, _), base, seq) ==
    LET f[i \in 0..Len(seq)] == IF i = 0 THEN base ELSE op(f[i - 1], seq[i]) IN f[Len(seq)]
ReplaceFirstSubSeq(r, s, t) ==
    LET at == {i \in 1..Len(t) - Len(s) + 1 : SubSeq(t, i, i + Len(s) - 1) = s}
        i == CHOOSE i \in at : \A j \in at : i <= j
    IN IF at = {} THEN t ELSE SubSeq(t, 1, i - 1) \o r \o SubSeq(t, i + Len(s), Len(t))
====
