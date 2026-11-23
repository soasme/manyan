---------------------------- MODULE LevelCheck ---------------------------------
(* How Manyan checks TLA+ expression levels and higher-order / INSTANCE
   operator constraints (manyan.c, expr_level, check_levels, check_ho_arg and
   check_def_levels), matching SANY's modular level system (Specifying Systems,
   §17.2).

   An expression has a level in 0..3 (constant, state, action, temporal). Each
   operator context imposes an upper bound on its operand (prime <= 1, set and
   ENABLED <= 2, id and [] <= 3) and produces a result level.

   A higher-order operator Apply(Op(_), v) == a_ctx(Op(arg)) (or equivalently a
   module Sub with CONSTANT Op(_), v instantiated WITH Op <- F, v <- actual)
   summarizes its constraints on Op and v without knowing F or actual:
     - op_max:   upper bound on Op's own level from a_ctx;
     - v_max:    upper bound on v's level from arg and a_ctx;
     - arg_min:  minimum level F's parameter must allow (level of arg at v = 0);
     - coparam:  whether v's level reaches arg (so actual's level must also
                 meet F's parameter upper bound).

   We also model two-hop forwarding: Outer(Op(_), v) == o_ctx(Apply(Op, arg_o))
   called as Outer(F, actual). The summary check must be sound with respect to
   direct macro-expansion (never accepting an invalid expansion), and exact
   whenever F is weight-1 in its parameter (id, prime, set). *)
EXTENDS Naturals

CONSTANTS Ctxs,      \* context wrappers: "id", "prime", "set", "enabled", "always"
          ArgKinds,  \* argument shapes passed to Op: "c0", "v1", "p2", "t3", "v", "set_v", "en_v", "pr_v"
          Levels     \* actual argument levels 0..3

VARIABLES f_ctx, a_ctx, o_ctx, arg_a, arg_o, actual
vars == <<f_ctx, a_ctx, o_ctx, arg_a, arg_o, actual>>

Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

Cap(c) == CASE c = "prime" -> 1
            [] c \in {"set", "enabled"} -> 2
            [] OTHER -> 3

Res(c, l) == CASE c = "prime" -> Max(2, l)
               [] c = "enabled" -> 1
               [] c = "always" -> 3
               [] OTHER -> l

(* Level and validity of an argument shape evaluated with parameter level vl. *)
ArgOK(ak, vl) == CASE ak = "set_v" -> vl <= 2
                   [] ak = "en_v"  -> vl <= 2
                   [] ak = "pr_v"  -> vl <= 1
                   [] OTHER        -> TRUE

ArgLvl(ak, vl) == CASE ak = "c0"    -> 0
                    [] ak = "v1"    -> 1
                    [] ak = "p2"    -> 2
                    [] ak = "t3"    -> 3
                    [] ak = "v"     -> vl
                    [] ak = "set_v" -> vl
                    [] ak = "en_v"  -> 1
                    [] ak = "pr_v"  -> Max(2, vl)

(* Whether parameter v's level reaches ak (collect_free_params in manyan.c). *)
ArgUsesParam(ak) == ak \in {"v", "set_v"}

(* Upper bound on v imposed directly by ak under outer bound cap. *)
ArgParamMax(ak, cap) == CASE ak = "v"     -> cap
                          [] ak = "set_v" -> Min(2, cap)
                          [] ak = "en_v"  -> 2
                          [] ak = "pr_v"  -> 1
                          [] OTHER        -> 3

-------------------------------------------------------------------------------
(* 1. Summary algorithm (check_levels + check_ho_arg in manyan.c). *)

(* Summary of F(a) == f_ctx(a). *)
FLevel == Res(f_ctx, 0)
FMax   == Cap(f_ctx)

(* Summary of Apply(Op(_), w) == a_ctx(Op(arg_a)). *)
ApplyArgBaseLvl == ArgLvl(arg_a, 0)
ApplyLevel      == Res(a_ctx, ApplyArgBaseLvl)
ApplyOK         == ArgOK(arg_a, 0) /\ ApplyArgBaseLvl <= Cap(a_ctx)
ApplyOpMax      == Cap(a_ctx)
ApplyWMax       == ArgParamMax(arg_a, Cap(a_ctx))
ApplyArgMin     == ApplyArgBaseLvl
ApplyCoparam    == ArgUsesParam(arg_a)

(* Summary of Outer(Op(_), v) == o_ctx(Apply(Op, arg_o)), propagating Op's
   constraints across the call Apply(Op, arg_o) as check_ho_arg does. *)
OuterArgBaseLvl == ArgLvl(arg_o, 0)
ApplyUsesW      == ArgUsesParam(arg_a) /\ a_ctx \in {"id", "prime", "set"}
OuterCallLvl    == Max(ApplyLevel, IF ApplyUsesW THEN OuterArgBaseLvl ELSE 0)
OuterOK ==
    /\ ApplyOK
    /\ ArgOK(arg_o, 0)
    /\ OuterArgBaseLvl <= ApplyWMax
    /\ OuterCallLvl <= Cap(o_ctx)
OuterOpMax   == Min(ApplyOpMax, IF a_ctx \in {"id", "prime", "set"} THEN Cap(o_ctx) ELSE 3)
OuterVMax    == ArgParamMax(arg_o, Min(ApplyWMax, IF ApplyUsesW THEN Cap(o_ctx) ELSE 3))
OuterArgMin  == Max(ApplyArgMin, IF ApplyCoparam THEN OuterArgBaseLvl ELSE 0)
OuterCoparam == ApplyCoparam /\ ArgUsesParam(arg_o)

(* Final check at call site Outer(F, actual). *)
SummaryOK ==
    /\ OuterOK
    /\ FLevel <= OuterOpMax
    /\ actual <= OuterVMax
    /\ OuterArgMin <= FMax
    /\ (OuterCoparam => actual <= FMax)

-------------------------------------------------------------------------------
(* 2. Reference semantics: direct macro-expansion of Outer(F, actual).
      w = arg_o[v := actual]; arg = arg_a[w := w]; body = o_ctx(a_ctx(f_ctx(arg))). *)

ExpWOK  == ArgOK(arg_o, actual)
ExpWLvl == ArgLvl(arg_o, actual)

ExpArgOK  == ExpWOK /\ ArgOK(arg_a, ExpWLvl)
ExpArgLvl == ArgLvl(arg_a, ExpWLvl)

ExpFOK  == ExpArgOK /\ ExpArgLvl <= Cap(f_ctx)
ExpFLvl == Res(f_ctx, ExpArgLvl)

ExpAOK  == ExpFOK /\ ExpFLvl <= Cap(a_ctx)
ExpALvl == Res(a_ctx, ExpFLvl)

DirectOK == ExpAOK /\ ExpALvl <= Cap(o_ctx)

-------------------------------------------------------------------------------
Init ==
    /\ f_ctx \in Ctxs
    /\ a_ctx \in Ctxs
    /\ o_ctx \in Ctxs
    /\ arg_a \in ArgKinds
    /\ arg_o \in ArgKinds
    /\ actual \in Levels

Next == UNCHANGED vars
Spec == Init /\ [][Next]_vars

(* Soundness: modular level checking NEVER accepts an invalid macro-expansion. *)
Sound == SummaryOK => DirectOK

(* Exactness for weight-1 operators F (matching SANY's modular level system):
   when F's level depends on its parameter and Apply's body is valid on its own,
   summary checking agrees with direct expansion whenever the call's inner
   arguments are valid in isolation. *)
ExactWeightOne ==
    (f_ctx \in {"id", "prime", "set"} /\ a_ctx \in {"id", "set", "always"} /\ o_ctx \in {"id", "set", "always"})
        => (SummaryOK = DirectOK)
================================================================================
