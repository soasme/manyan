import Ref.Syntax

/-!
# The meaning of a constant expression

`sem O w n σ ρ e` is the value of `e` in the states `σ`, where the
names are bound as `ρ` says and the module's as `w` says, following
*Specifying Systems* (chapter 16) and the definitions of the standard
modules. Evaluation nests at most `n` deep.

Where TLA⁺ does not say what a value is (`<<>>[1]`, `1 = "a"`,
`CHOOSE x \in {} : TRUE`), the result is `undef`: any value is right.
Logic is strict: a connective or quantifier whose operand is not known
to be a Boolean is `undef`, though TLC may answer.

Some questions have answers no program computes: whether `\A x \in Nat :
P` holds, or which element `CHOOSE` takes. The oracle `O` answers them.
`Oracle.classical χ` answers each as TLA⁺ does, with `χ` the choice
function, so `sem (Oracle.classical χ)` is the definition; it is not
computable. `Oracle.exec` answers what is computable and is `unknown`
otherwise, so `sem Oracle.exec` is a reference to run, as TLC is one
specialized to finite models.
-/
namespace Ref

structure Oracle where
  /-- `\A v \in S : p v`, for a set `S` (membership `mem`) not enumerated. -/
  all : (mem p : Val → M Bool) → M Bool
  /-- Whether two sets, one of them not enumerated, are equal. -/
  same : (memA memB : Val → M Bool) → M Bool
  /-- `IsFiniteSet(S)` and `Cardinality(S)`, for a set not enumerated. -/
  finite : (eq : Val → Val → M Bool) → (mem : Val → M Bool) → M Bool
  card : (eq : Val → Val → M Bool) → (mem : Val → M Bool) → M Nat
  /-- `CHOOSE` among the values `sat` holds of: `some` of them, if enumerated. -/
  choose : (sat : Val → M Bool) → Option (List Val) → M Val

def Oracle.exec : Oracle where
  all _ _ := unknown "a quantifier over a set not enumerated"
  same _ _ := unknown "the equality of a set not enumerated"
  finite _ _ := unknown "whether a set not enumerated is finite"
  card _ _ := unknown "the cardinality of a set not enumerated"
  choose _
    | some [w] => pure w
    | some [] => undef "CHOOSE with no value that satisfies it"
    | some _ => unknown "CHOOSE among several values: that is the choice function's"
    | none => unknown "CHOOSE from a set not enumerated"

/-- `=` between values with nothing kept unevaluated, as the evaluator
computes it where it answers (`Ref/Choice.lean`): sets with the same
elements, functions with the same graph, and values of different kinds
apart. -/
def Val.feq : Val → Val → Bool
  | .bool x, .bool y => x == y
  | .int x, .int y => x == y
  | .str x, .str y => x == y
  | .model x, .model y => x == y
  | .set x, .set y =>
    x.attach.all (fun ⟨a, _⟩ => y.attach.any fun ⟨b, _⟩ => feq a b) &&
    y.attach.all (fun ⟨b, _⟩ => x.attach.any fun ⟨a, _⟩ => feq a b)
  | .fcn x, .fcn y =>
    x.attach.all (fun ⟨p, _⟩ => y.attach.any fun ⟨q, _⟩ => feq p.1 q.1) &&
    y.attach.all (fun ⟨q, _⟩ => x.attach.any fun ⟨p, _⟩ => feq p.1 q.1) &&
    x.attach.all (fun ⟨p, _⟩ => y.attach.all fun ⟨q, _⟩ => !feq p.1 q.1 || feq p.2 q.2)
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ x›; have := List.sizeOf_lt_of_mem ‹_ ∈ y›; omega)
    | (have := List.sizeOf_lt_of_mem ‹p ∈ x›; have := List.sizeOf_lt_of_mem ‹q ∈ y›
       cases p; cases q; simp at *; omega)

/-- A total answer to a question: `ok` for every value, or `undef`. -/
def total (f : Val → M Bool) : Prop := ∀ v, f v = .ok true ∨ f v = .ok false

open Classical in
noncomputable def Oracle.classical (χ : (Val → Prop) → Val) : Oracle where
  all mem p :=
    if total mem ∧ ∀ v, mem v = .ok true → p v = .ok true ∨ p v = .ok false then
      pure (decide (∀ v, mem v = .ok true → p v = .ok true))
    else undef "a quantifier whose set or body TLA⁺ leaves unspecified"
  same a b :=
    if total a ∧ total b then pure (decide (∀ v, a v = b v))
    else undef "the equality of a set TLA⁺ leaves unspecified"
  finite eq mem :=
    if total mem then pure (decide (∃ l : List Val, ∀ v, mem v = .ok true → ∃ w ∈ l, eq v w = .ok true))
    else undef "a set TLA⁺ leaves unspecified"
  card eq mem :=
    if h : total mem ∧ ∃ k, ∃ l : List Val, l.length = k ∧ (∀ w ∈ l, mem w = .ok true) ∧
        (∀ v, mem v = .ok true → ∃ w ∈ l, eq v w = .ok true) ∧
        l.Pairwise (fun a b => eq a b = .ok false) then
      -- Every such list has the same length.
      pure (Classical.choose h.2)
    else undef "the cardinality of an infinite set"
  -- From an enumerated set, the elements that satisfy P: χ's choice of
  -- a value equal to one of them, as the enumeration has it.
  choose sat
    | some [] => undef "CHOOSE with no value that satisfies it"
    | some l@(w :: _) =>
      pure ((l.find? (Val.feq (χ fun v => ∃ u ∈ l, v.feq u = true))).getD w)
    | none =>
      if total sat ∧ ∃ v, sat v = .ok true then pure (χ (fun v => sat v = .ok true))
      else undef "CHOOSE with no value that satisfies it"

/-! ## Values -/

def Val.isSet : Val → Bool
  | .set _ => true
  | .lazy (.fcn ..) => false
  | .lazy _ => true
  | _ => false

def Val.isFcn : Val → Bool
  | .fcn _ | .lazy (.fcn ..) => true
  | _ => false

/-- A set the reference keeps unevaluated that is certainly infinite. -/
def Lazy.infinite : Lazy → Bool
  | .nat | .int | .string => true
  | .cup (.lazy a) (.lazy b) => a.infinite || b.infinite
  | .cup (.lazy a) _ | .cup _ (.lazy a) => a.infinite
  | .diff (.lazy a) (.set _) => a.infinite
  | .seq (.set (_ :: _)) => true
  | _ => false

def tuple (vs : List Val) : Val :=
  .fcn ((List.range vs.length).map (fun i => Val.int (i + 1 : Nat)) |>.zip vs)

/-- The elements of a sequence, a function with the domain 1..n. -/
def Val.seq? : Val → Option (List Val)
  | .fcn g => (List.range g.length).mapM fun i =>
      -- A function's keys are distinct, so they are 1..n if each of 1..n is one.
      (g.find? fun (k, _) => match k with | .int j => j == i + 1 | _ => false).map Prod.snd
  | _ => none

/-- How many elements an enumeration may have. -/
def limit : Nat := 100000

def asBool : Val → M Bool
  | .bool b => pure b
  | _ => undef "a Boolean operand that is not a Boolean"

def asInt : Val → M Int
  | .int n => pure n
  | _ => undef "an integer operand that is not an integer"

def asSet : Val → M (List Val)
  | .set l => pure l
  | .lazy s => if s.infinite then undef "an infinite set where a finite one is needed"
               else unknown "a set not enumerated where its elements are needed"
  | _ => undef "a set operand that is not a set"

/-- `TRUE` if one is, `FALSE` if all are, else the first that is neither:
an unspecified Boolean (as `1 = "a"`) leaves `\/` unspecified only when
nothing else is `TRUE`. -/
def anyOf : List (M Bool) → M Bool
  | [] => pure false
  | .ok true :: _ => pure true
  | .ok false :: rest => anyOf rest
  | .error e :: rest => match anyOf rest with
    | .ok true => pure true
    | _ => .error e

def allOf (l : List (M Bool)) : M Bool :=
  (! ·) <$> anyOf (l.map fun r => (! ·) <$> r)

/-- Strict: every operand must be a Boolean. -/
def strictAll (l : List (M Bool)) : M Bool := do
  let bs ← l.mapM id
  pure (bs.all id)

/-! ## One level of evaluation

The steps are given the functions that evaluate one level deeper as a
`Ctx`; `tie` ties them, so no definition is recursive but `tie`, on the
depth. -/

/-- What a module and its model give: the definitions (constants
included), the variables, and the universe, the states a behavior may
take, which `ENABLED` ranges over. -/
structure World where
  defs : Env := []
  vars : List String := []
  states : List State := []

structure Ctx where
  O : Oracle
  w : World
  ev : St → Env → Expr → M Val
  mem : Val → Val → M Bool
  eq : Val → Val → M Bool
  app : Val → Val → M Val

namespace Ctx
variable (c : Ctx)

/-- `{vs}`, each value once. -/
def mkSet (vs : List Val) : M Val :=
  if vs.length > limit then unknown "a set too large to enumerate" else
  .set <$> vs.foldlM (fun out v => do
    pure (if ← anyOf (out.map (c.eq v)) then out else out ++ [v])) []

def mkFcn (g : List (Val × Val)) : M Val :=
  .fcn <$> g.foldlM (fun out (k, v) => do
    if ← anyOf (out.map fun (k', _) => c.eq k k') then undef "a function that maps a value twice"
    pure (out ++ [(k, v)])) []

def all (S : Val) (p : Val → M Bool) : M Bool :=
  match S with
  | .set l => strictAll (l.map p)
  | .lazy (.fcn ..) | .bool _ | .int _ | .str _ | .model _ | .fcn _ => undef "a quantifier over a value that is not a set"
  | .lazy _ => c.O.all (c.mem · S) p

def any (S : Val) (p : Val → M Bool) : M Bool :=
  (! ·) <$> c.all S (fun v => (! ·) <$> p v)

def subseteq (A B : Val) : M Bool := c.all A (c.mem · B)

def domain : Val → M Val
  | .fcn g => pure (.set (g.map Prod.fst))
  | .lazy (.fcn d ..) => pure d
  | _ => undef "DOMAIN of a value that is not a function"

/-- The tuples of factors, or `none` if there are more than `limit`. -/
def tuples : List (List Val) → Option (List (List Val))
  | [] => some [[]]
  | f :: fs => do
    let rest ← tuples fs
    if f.length * rest.length > limit then none
    else some (f.flatMap fun v => rest.map (v :: ·))

def product (factors : List Val) : M Val := do
  let sets ← factors.mapM fun f => match f with
    | .set l => pure (some l)
    | .lazy _ => if f.isSet then pure none else undef "\\X of a value that is not a set"
    | _ => undef "\\X of a value that is not a set"
  if sets.any (fun s => match s with | some [] => true | _ => false) then return .set []
  match sets.mapM id with
  | some ls => match tuples ls with
    | some ts => pure (.set (ts.map tuple))
    | none => pure (.lazy (.product factors))
  | none => pure (.lazy (.product factors))

def funSet (A B : Val) : M Val := do
  if !A.isSet || !B.isSet then undef "[S -> T] of a value that is not a set" else
  match A, B with
  | .set [], _ => pure (.set [.fcn []])
  | .set _, .set [] => pure (.set [])
  | .set ks, .set vs => match tuples (ks.map fun _ => vs) with
    | some ts => pure (.set (ts.map fun t => .fcn (ks.zip t)))
    | none => pure (.lazy (.funSet A B))
  | _, _ => pure (.lazy (.funSet A B))

def recordSet (fields : List (String × Val)) : M Val := do
  let p ← product (fields.map Prod.snd)
  match p with
  | .set ts => pure (.set (ts.map fun
      | .fcn g => .fcn (fields.map (fun (f, _) => Val.str f) |>.zip (g.map Prod.snd))
      | v => v))
  | _ => pure (.lazy (.recordSet fields))

/-- `[f EXCEPT !path = e]`, with `@` the value it replaces. Outside the
domain the function is unchanged: `[x \in DOMAIN f |-> IF x = k ...]`. -/
def update (σ : St) (ρ : Env) (f : Val) : List Val → Expr → M Val
  | [], e => c.ev σ (("@", .val f) :: ρ) e
  | k :: path, e => match f with
    | .fcn g => .fcn <$> g.mapM fun (k', v) => do
      if ← c.eq k k' then pure (k', ← update σ ρ v path e) else pure (k', v)
    | _ => unknown "EXCEPT of a function not enumerated"

def constant : String → M Val
  | "Nat" => pure (.lazy .nat)
  | "Int" => pure (.lazy .int)
  | "STRING" => pure (.lazy .string)
  | "BOOLEAN" => pure (.set [.bool false, .bool true])
  | "TRUE" => pure (.bool true)
  | "FALSE" => pure (.bool false)
  | "$any" => unknown "a quantifier or CHOOSE over all values"
  | x => unknown s!"the name {x}"

def binder (σ : St) (ρ : Env) (b : Binder) (x : String) (S : Val) (body : Expr) : M Val :=
  let at_ (v : Val) := c.ev σ ((x, .val v) :: ρ) body
  let test (v : Val) := at_ v >>= asBool
  match b with
  | .all => .bool <$> c.all S test
  | .ex => .bool <$> c.any S test
  | .choose => match S with
    | .set l => do
      let sat ← l.filterM test
      c.O.choose (fun v => do pure ((← c.mem v S) && (← test v))) (some sat)
    | _ => if S.isSet then c.O.choose (fun v => do pure ((← c.mem v S) && (← test v))) none
           else undef "CHOOSE from a value that is not a set"
  | .filter => match S with
    | .set l => do c.mkSet (← l.filterM test)
    | _ => if S.isSet then pure (.lazy (.filter S x body ρ σ)) else undef "{x \\in S : P} of a value that is not a set"
  | .map => do c.mkSet (← (← asSet S).mapM at_)
  | .fcn => match S with
    | .set l => do c.mkFcn (← l.mapM fun v => do pure (v, ← at_ v))
    | _ => if S.isSet then pure (.lazy (.fcn S x body ρ σ)) else undef "[x \\in S |-> e] of a value that is not a set"
  | .recfcn => if S.isSet then pure (.lazy (.fcn S x body ρ σ)) else undef "f[x \\in S] == e of a value that is not a set"
  | .select => match S.seq? with
    | some l => tuple <$> l.filterM test
    | none => undef "SelectSeq of a value that is not a sequence"

/-- An operator of Integers, if `o` is one. -/
def arith (o : String) : Option (Int → Int → M Val) :=
  match o with
  | "+" => some fun a b => pure (.int (a + b))
  | "-" => some fun a b => pure (.int (a - b))
  | "*" => some fun a b => pure (.int (a * b))
  -- a \div b and a % b are defined for b > 0, rounding down.
  | "\\div" => some fun a b => if b > 0 then pure (.int (a / b)) else undef "\\div by a number that is not positive"
  | "%" => some fun a b => if b > 0 then pure (.int (a % b)) else undef "% by a number that is not positive"
  | "^" => some fun a b => if b > 0 || (b == 0 && a != 0) then pure (.int (a ^ b.toNat)) else undef "^ to a negative power, or 0^0"
  | "<" => some fun a b => pure (.bool (a < b))
  | ">" => some fun a b => pure (.bool (a > b))
  | "<=" => some fun a b => pure (.bool (a ≤ b))
  | ">=" => some fun a b => pure (.bool (a ≥ b))
  | ".." => some fun a b => if b - a ≥ limit then unknown "a range too large to enumerate"
            else pure (.set ((List.range (b - a + 1).toNat).map fun (i : Nat) => .int (a + i)))
  | _ => none

def seqArg (v : Val) : M (List Val) :=
  match v.seq? with
  | some l => pure l
  | none => undef "a sequence operand that is not a sequence"

/-- An operator of one argument applied to its value. -/
def strict1 (o : String) (S : Val) : M Val :=
  match o with
  | "~" => .bool <$> (! ·) <$> asBool S
  | "-." => do pure (.int (- (← asInt S)))
  | "DOMAIN" => domain S
  | "UNION" => do
    let members ← asSet S
    if !members.all Val.isSet then undef "UNION of a set of values that are not sets" else
    match members.mapM (fun m => match m with | .set l => some l | _ => none) with
    | some ls => c.mkSet ls.flatten
    | none => pure (.lazy (.union members))
  | "SUBSET" => match S with
    | .set l => if l.length > 16 then pure (.lazy (.subset S))
                else pure (.set (l.foldr (fun v acc => acc ++ acc.map (fun s => match s with
                  | .set m => .set (v :: m) | s => s)) [.set []]))
    | _ => if S.isSet then pure (.lazy (.subset S)) else undef "SUBSET of a value that is not a set"
  | "Seq" => match S with
    | .set [] => pure (.set [tuple []])
    | _ => if S.isSet then pure (.lazy (.seq S)) else undef "Seq of a value that is not a set"
  | "Cardinality" => match S with
    | .set l => pure (.int l.length)
    | .lazy s => if s.infinite then undef "the cardinality of an infinite set"
                 else if S.isSet then .int <$> c.O.card c.eq (c.mem · S)
                 else undef "Cardinality of a value that is not a set"
    | _ => undef "Cardinality of a value that is not a set"
  | "IsFiniteSet" => match S with
    | .set _ => pure (.bool true)
    | .lazy s => if s.infinite then pure (.bool false)
                 else if S.isSet then .bool <$> c.O.finite c.eq (c.mem · S)
                 else undef "IsFiniteSet of a value that is not a set"
    | _ => undef "IsFiniteSet of a value that is not a set"
  -- Sequences.
  | "Len" => do pure (.int (← seqArg S).length)
  | "Head" => c.app S (.int 1)
  | "Tail" => do
    match ← seqArg S with
    | [] => undef "Tail of the empty sequence"
    | _ :: rest => pure (tuple rest)
  | _ => unknown s!"the operator {o} with 1 arguments"

/-- An operator of two arguments applied to their values. -/
def strict2 (o : String) (A B : Val) : M Val :=
  match o with
  | "/\\" => .bool <$> strictAll [asBool A, asBool B]
  | "\\/" => do let x ← asBool A; let y ← asBool B; pure (.bool (x || y))
  | "=>" => do let x ← asBool A; let y ← asBool B; pure (.bool (!x || y))
  | "<=>" => do let x ← asBool A; let y ← asBool B; pure (.bool (x == y))
  | "=" => .bool <$> c.eq A B
  | "#" => .bool <$> (! ·) <$> c.eq A B
  | "\\in" => .bool <$> c.mem A B
  | "\\notin" => .bool <$> (! ·) <$> c.mem A B
  | "\\subseteq" => .bool <$> c.subseteq A B
  | "\\subset" => do pure (.bool ((← c.subseteq A B) && !(← c.eq A B)))
  | "app" => c.app A B
  | "\\cup" => match A, B with
    | .set a, .set b => c.mkSet (a ++ b)
    | _, _ => if A.isSet && B.isSet then pure (.lazy (.cup A B)) else undef "\\cup of a value that is not a set"
  | "\\cap" => match A, B with
    | .set a, _ => do c.mkSet (← a.filterM (c.mem · B))
    | _, .set b => do c.mkSet (← b.filterM (c.mem · A))
    | _, _ => if A.isSet && B.isSet then pure (.lazy (.diff A (.lazy (.diff A B))))
              else undef "\\cap of a value that is not a set"
  | "\\" => match A with
    | .set a => do if !B.isSet then undef "\\ of a value that is not a set" else c.mkSet (← a.filterM fun v => (! ·) <$> c.mem v B)
    | _ => if A.isSet && B.isSet then pure (.lazy (.diff A B)) else undef "\\ of a value that is not a set"
  | "->" => funSet A B
  | "Append" => do pure (tuple ((← seqArg A) ++ [B]))
  | "\\o" => do pure (tuple ((← seqArg A) ++ (← seqArg B)))
  -- TLC: d :> e == [x \in {d} |-> e], and f @@ g, f's where both map.
  | ":>" => pure (.fcn [(A, B)])
  | "@@" => match A, B with
    | .fcn a, .fcn b => do
      let rest ← b.filterM fun (k, _) => (! ·) <$> anyOf (a.map fun (k', _) => c.eq k k')
      pure (.fcn (a ++ rest))
    | _, _ => if A.isFcn && B.isFcn then unknown "@@ of a function not enumerated"
              else undef "@@ of a value that is not a function"
  | _ => match arith o with
    | some f => do f (← asInt A) (← asInt B)
    | none => unknown s!"the operator {o}"

/-- An operator applied to the values of its arguments. -/
def strict (o : String) (vs : List Val) : M Val :=
  match o, vs with
  | "{}", _ => c.mkSet vs
  | "<<>>", _ => pure (tuple vs)
  | "\\X", _ => product vs
  | _, [a] => c.strict1 o a
  | _, [a, b] => c.strict2 o a b
  | "SubSeq", [s, m, n] => do
    let m ← asInt m
    let n ← asInt n
    let _ ← seqArg s
    let k := (1 + n - m).toNat
    tuple <$> (List.range k).mapM fun (i : Nat) => c.app s (.int (i + m))
  | _, _ => unknown s!"the operator {o} with {vs.length} arguments"

/-- A state variable's value: in the next state, under a prime. -/
def var (σ : St) (x : String) : M Val :=
  if σ.primed then match σ.nxt with
    | some t => match t.lookup x with
      | some v => pure v
      | none => unknown s!"the variable {x} in the next state"
    | none => undef s!"{x}' where there is no next state"
  else match σ.cur.lookup x with
    | some v => pure v
    | none => undef s!"the variable {x} where there is no state"

/-- An argument for a parameter: an operator for `LAMBDA` or an
operator's name, else the expression, evaluated where it is used. -/
def arg (ρ : Env) : Expr → Def
  | .lambda ps e => .op ps e ρ
  | e@(.name g) => match ρ.lookup g <|> c.w.defs.lookup g with
    | some d@(.op (_ :: _) _ _) => d
    | _ => .expr e ρ
  | e => .expr e ρ

/-- What a name stands for, or `none` for a variable or a built-in. -/
def lookup (ρ : Env) (x : String) : Option Def := ρ.lookup x <|> c.w.defs.lookup x

/-- `UNCHANGED e`, that is `e' = e`. -/
def unchanged (σ : St) (ρ : Env) (e : Expr) : M Bool := do
  if σ.primed then undef "UNCHANGED under a prime" else
  c.eq (← c.ev (.mk σ.cur σ.nxt true) ρ e) (← c.ev σ ρ e)

/-- A function of a recursive definition on a finite domain, enumerated
for an operator that needs its graph. -/
def force (v : Val) : M Val :=
  match v with
  | .lazy (.fcn (.set ks) ..) => do c.mkFcn (← ks.mapM fun k => do pure (k, ← c.app v k))
  | v => pure v

def op (σ : St) (ρ : Env) (o : String) (args : List Expr) : M Val :=
  match c.lookup ρ o, args with
  | some (.op ps body ρ'), _ =>
    if ps.length != args.length then undef s!"{o} applied to {args.length} arguments"
    else c.ev σ (ps.zip (args.map (c.arg ρ)) ++ ρ') body
  | some _, _ => undef s!"{o} applied to arguments, though it takes none"
  -- IF evaluates only the branch it takes.
  | none, [p, a, b] => if o == "IF" then do c.ev σ ρ (if ← (c.ev σ ρ p >>= asBool) then a else b)
                       else strictOp
  | none, [e] => match o with
    | "'" => if σ.primed then undef "a primed expression primed again"
             else c.ev (.mk σ.cur σ.nxt true) ρ e
    | "UNCHANGED" => do .bool <$> c.unchanged σ ρ e
    -- ENABLED A: some state of the universe is a next state A allows.
    | "ENABLED" => if σ.primed then undef "ENABLED under a prime" else
      .bool <$> anyOf (c.w.states.map fun t => c.ev (.mk σ.cur (some t) false) ρ e >>= asBool)
    | "[]" | "<>" => unknown "a temporal formula where a value is needed"
    | _ => strictOp
  | none, [a, v] => match o with
    | "[A]_" => do let x ← c.ev σ ρ a >>= asBool; let u ← c.unchanged σ ρ v; pure (.bool (x || u))
    | "<<A>>_" => do let x ← c.ev σ ρ a >>= asBool; let u ← c.unchanged σ ρ v; pure (.bool (x && !u))
    | "~>" | "WF_" | "SF_" => unknown "a temporal formula where a value is needed"
    | _ => strictOp
  | none, _ => strictOp
where
  strictOp := do c.strict o (← (← args.mapM (c.ev σ ρ)).mapM c.force)

def eval (σ : St) (ρ : Env) : Expr → M Val
  | .bool b => pure (.bool b)
  | .int n => pure (.int n)
  | .str s => pure (.str s)
  | .name x => match c.lookup ρ x with
    | some (.val v) => pure v
    | some (.expr d ρ') => c.ev σ ρ' d
    | some (.op [] d ρ') => c.ev σ ρ' d
    | some (.op ..) => undef s!"the operator {x} without its arguments"
    | none => if c.w.vars.contains x then var σ x else constant x
  | .op o args => c.op σ ρ o args
  | .lambda .. => undef "LAMBDA where a value is needed"
  | .bind b x s body => do c.binder σ ρ b x (← c.ev σ ρ s >>= c.force) body
  | .record fields => do c.mkFcn (← fields.mapM fun (f, e) => do pure (.str f, ← c.ev σ ρ e))
  | .recordSet fields => do recordSet (← fields.mapM fun (f, e) => do pure (f, ← c.ev σ ρ e))
  | .except f updates => do
    updates.foldlM (fun v (path, e) => do c.update σ ρ v (← path.mapM (c.ev σ ρ)) e) (← c.ev σ ρ f >>= c.force)
  | .letIn x ps d body => c.ev σ ((x, if ps.isEmpty then .expr d ρ else .op ps d ρ) :: ρ) body
  | .case arms other => do
    let guards ← arms.mapM fun (p, _) => c.ev σ ρ p >>= asBool
    let taken := (arms.zip guards).filter (·.2) |>.map (·.1.2)
    match taken, other with
    | [], some e => c.ev σ ρ e
    | [], none => undef "CASE with no true guard"
    | [e], _ => c.ev σ ρ e
    | e :: es, _ => do
      -- CASE is a CHOOSE among the values of the true arms.
      let v ← c.ev σ ρ e
      if ← allOf ((← es.mapM (c.ev σ ρ)).map (c.eq v)) then pure v
      else unknown "CASE among true arms of different values: that is the choice function's"

/-- `v \in S`. -/
def member (v : Val) : Val → M Bool
  | .set l => anyOf (l.map (c.eq v))
  | .lazy s => match s with
    | .nat => pure (match v with | .int n => n ≥ 0 | _ => false)
    | .int => pure (match v with | .int _ => true | _ => false)
    | .string => pure (match v with | .str _ => true | _ => false)
    | .filter S x p ρ σ => do
      if !(← c.mem v S) then return false
      c.ev σ ((x, .val v) :: ρ) p >>= asBool
    | .cup A B => anyOf [c.mem v A, c.mem v B]
    | .diff A B => do pure ((← c.mem v A) && !(← c.mem v B))
    | .union sets => anyOf (sets.map (c.mem v))
    | .subset S => if v.isSet then c.subseteq v S else pure false
    | .product fs => match v.seq? with
      | some l => if l.length == fs.length then allOf ((l.zip fs).map fun (x, F) => c.mem x F) else pure false
      | none => pure false
    | .seq S => match v.seq? with
      | some l => allOf (l.map (c.mem · S))
      | none => pure false
    | .funSet A B => if !v.isFcn then pure false else do
      if !(← c.eq (← domain v) A) then return false
      c.all A fun k => do c.mem (← c.app v k) B
    | .recordSet fields => match v with
      | .fcn g => do
        if !(← c.eq (.set (g.map Prod.fst)) (.set (fields.map (Val.str ·.1)))) then return false
        allOf (fields.map fun (f, S) => do c.mem (← c.app v (.str f)) S)
      | _ => pure false
    | .fcn .. => undef "\\in a function"
  | _ => undef "\\in a value that is not a set"

/-- `a = b`: extensional, and unspecified between values of different
kinds, as a string and a set. -/
def equal (a b : Val) : M Bool :=
  match a, b with
  | .bool x, .bool y => pure (x == y)
  | .int x, .int y => pure (x == y)
  | .str x, .str y => pure (x == y)
  | .model x, .model y => pure (x == y)
  | .set x, .set y => allOf ((x.map (c.mem · b)) ++ (y.map (c.mem · a)))
  | .fcn x, .fcn y => do
    if !(← c.eq (.set (x.map Prod.fst)) (.set (y.map Prod.fst))) then return false
    allOf (x.map fun (k, v) => do c.eq v (← c.app b k))
  | _, _ =>
    if a.isFcn && b.isFcn then do
      if !(← c.eq (← domain a) (← domain b)) then return false
      c.all (← domain a) fun k => do c.eq (← c.app a k) (← c.app b k)
    else if a.isSet && b.isSet then
      match a, b with
      | .lazy .nat, .lazy .nat | .lazy .int, .lazy .int | .lazy .string, .lazy .string => pure true
      | .lazy s, .set _ | .set _, .lazy s => if s.infinite then pure false else c.O.same (c.mem · a) (c.mem · b)
      | _, _ => c.O.same (c.mem · a) (c.mem · b)
    else undef "= between values of different kinds"

/-- The value a function's graph maps `a` to. -/
def lookupIn (a : Val) : List (Val × Val) → M Val
  | [] => undef "a function applied outside its domain"
  | (k, v) :: g => do if ← c.eq a k then pure v else lookupIn a g

/-- `f[a]`. -/
def apply (f a : Val) : M Val :=
  match f with
  | .fcn g => c.lookupIn a g
  | .lazy (.fcn S x e ρ σ) => do
    -- `$self` is the function, in the body of a recursive definition.
    if ← c.mem a S then c.ev σ ((x, .val a) :: ("$self", .val f) :: ρ) e
    else undef "a function applied outside its domain"
  | _ => undef "application of a value that is not a function"

end Ctx

def tie (O : Oracle) (w : World) : Nat → Ctx
  | 0 =>
    let deep {α} : M α := unknown "an expression nested too deep"
    { O, w, ev := fun _ _ _ => deep, mem := fun _ _ => deep, eq := fun _ _ => deep, app := fun _ _ => deep }
  | n + 1 =>
    let c := tie O w n
    { O, w, ev := c.eval, mem := c.member, eq := c.equal, app := c.apply }

def sem (O : Oracle) (w : World) (n : Nat) (σ : St) (ρ : Env) (e : Expr) : M Val := (tie O w n).ev σ ρ e

end Ref
