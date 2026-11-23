--------------------------------- MODULE MCFmt ---------------------------------
(* Exhaustive check of Manyan's formatter parenthesization (RoundTrip and
   Idempotent over every AST up to depth 2 using all TLA+ operator classes)
   and comment-stream cursor (CommentsPreserved over all comment placements). *)
EXTENDS Fmt

Atoms == {[kind |-> "var", name |-> "x"]}

Unary(S) ==
    {[kind |-> "op", op |-> op, args |-> <<e>>] : op \in {"~", "-.", "ENABLED", "[]", "'"}, e \in S}

Binary(S) ==
    {[kind |-> "op", op |-> op, args |-> <<a, b>>] : op \in {"+", "/\\", "=", "=>"}, a \in S, b \in Atoms}
    \cup {[kind |-> "op", op |-> op, args |-> <<a, b>>] : op \in {"+", "/\\", "=", "=>"}, a \in Atoms, b \in S}

Ifs(S) ==
    {[kind |-> "if", args |-> <<a, b>>] : a \in Atoms, b \in S}

D1 == Atoms \cup Unary(Atoms) \cup Binary(Atoms) \cup Ifs(Atoms)
AllExprs == D1 \cup Unary(D1) \cup Binary(D1) \cup Ifs(D1)

(* Two spans on lines 2 and 4 (positions 10 and 20), with 0..3 comments at
   distinct sorted positions before, between, trailing, or after the spans. *)
TwoSpans == <<[pos |-> 10, eline |-> 2], [pos |-> 20, eline |-> 4]>>
Com(p, l, inl) == [pos |-> p, line |-> l, inline |-> inl]
ComPool == {Com(5, 1, FALSE), Com(12, 2, TRUE), Com(15, 3, FALSE), Com(22, 4, TRUE), Com(25, 5, FALSE)}

AllCommentCases ==
    {[spans |-> TwoSpans, comments |-> <<>>]}
    \cup {[spans |-> TwoSpans, comments |-> <<c1>>] : c1 \in ComPool}
    \cup {[spans |-> TwoSpans, comments |-> p] :
             p \in {q \in ComPool \X ComPool : q[1].pos < q[2].pos}}
    \cup {[spans |-> TwoSpans, comments |-> t] :
             t \in {q \in ComPool \X ComPool \X ComPool : q[1].pos < q[2].pos /\ q[2].pos < q[3].pos}}
================================================================================
CONSTANT Exprs <- AllExprs
CONSTANT CommentCases <- AllCommentCases
SPECIFICATION Spec
INVARIANT RoundTrip Idempotent CommentsPreserved
CHECK_DEADLOCK FALSE
