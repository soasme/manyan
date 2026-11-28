---- MODULE SequencesExt ----
\* CommunityModules' SetToSeq, with its definition: TLC replaces it by its
\* Java, as Manyan by its own.
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : \A i, j \in DOMAIN f : f[i] = f[j] => i = j
FoldLeft(op(_, _), base, seq) ==
    LET f[i \in 0..Len(seq)] == IF i = 0 THEN base ELSE op(f[i - 1], seq[i]) IN f[Len(seq)]
ReplaceFirstSubSeq(r, s, t) ==
    LET at == {i \in 1..Len(t) - Len(s) + 1 : SubSeq(t, i, i + Len(s) - 1) = s}
        i == CHOOSE i \in at : \A j \in at : i <= j
    IN IF at = {} THEN t ELSE SubSeq(t, 1, i - 1) \o r \o SubSeq(t, i + Len(s), Len(t))
====
