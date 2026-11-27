---- MODULE assume_level_decls ----
\* Declarations of levels, with NEW or not, in an ASSUME ... PROVE.
THEOREM ASSUME STATE s, NEW ACTION a, TEMPORAL A(_), NEW c \in {}, CONSTANT d
        PROVE s
====
