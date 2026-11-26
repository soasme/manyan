import Ref.Syntax

/-!
# The meaning of a constant expression

`sem O n ρ e` is the value of `e` where the names are bound as `ρ` says,
following *Specifying Systems* (chapter 16) and the definitions of the
standard modules. Evaluation nests at most `n` deep.

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
  choose sat _ :=
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

structure Ctx where
  O : Oracle
  ev : Env → Expr → M Val
  mem : Val → Val → M Bool
  eq : Val → Val → M Bool
  app : Val → Val → M Val

namespace Ctx
variable (c : Ctx)

/-- `{vs}`, each value once. -/
def mkSet (vs : List Val) : M Val := do
  if vs.length > limit then unknown "a set too large to enumerate" else
  let mut out : Array Val := #[]
  for v in vs do
    if !(← anyOf (out.toList.map (c.eq v))) then out := out.push v
  pure (.set out.toList)

def mkFcn (g : List (Val × Val)) : M Val := do
  let mut out : Array (Val × Val) := #[]
  for (k, v) in g do
    if ← anyOf (out.toList.map fun (k', _) => c.eq k k') then
      undef "a function that maps a value twice"
    out := out.push (k, v)
  pure (.fcn out.toList)

def all (S : Val) (p : Val → M Bool) : M Bool :=
  match S with
  | .set l => strictAll (l.map p)
  | .lazy (.fcn ..) | .bool _ | .int _ | .str _ | .fcn _ => undef "a quantifier over a value that is not a set"
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
def update (ρ : Env) (f : Val) : List Val → Expr → M Val
  | [], e => c.ev (("@", .val f) :: ρ) e
  | k :: path, e => match f with
    | .fcn g => do
      let mut out := #[]
      for (k', v) in g do
        if ← c.eq k k' then out := out.push (k', ← update ρ v path e)
        else out := out.push (k', v)
      pure (.fcn out.toList)
    | _ => unknown "EXCEPT of a function not enumerated"

def constant : String → M Val
  | "Nat" => pure (.lazy .nat)
  | "Int" => pure (.lazy .int)
  | "STRING" => pure (.lazy .string)
  | "BOOLEAN" => pure (.set [.bool false, .bool true])
  | x => unknown s!"the name {x}"

def binder (ρ : Env) (b : Binder) (x : String) (S : Val) (body : Expr) : M Val :=
  let at_ (v : Val) := c.ev ((x, .val v) :: ρ) body
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
    | _ => if S.isSet then pure (.lazy (.filter S x body ρ)) else undef "{x \\in S : P} of a value that is not a set"
  | .map => do c.mkSet (← (← asSet S).mapM at_)
  | .fcn => match S with
    | .set l => do c.mkFcn (← l.mapM fun v => do pure (v, ← at_ v))
    | _ => if S.isSet then pure (.lazy (.fcn S x body ρ)) else undef "[x \\in S |-> e] of a value that is not a set"
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

/-- An operator applied to the values of its arguments. -/
def strict (o : String) (vs : List Val) : M Val :=
  match o, vs with
  | "~", [a] => .bool <$> (! ·) <$> asBool a
  | "/\\", [a, b] => .bool <$> strictAll [asBool a, asBool b]
  | "\\/", [a, b] => do let x ← asBool a; let y ← asBool b; pure (.bool (x || y))
  | "=>", [a, b] => do let x ← asBool a; let y ← asBool b; pure (.bool (!x || y))
  | "<=>", [a, b] => do let x ← asBool a; let y ← asBool b; pure (.bool (x == y))
  | "=", [a, b] => .bool <$> c.eq a b
  | "#", [a, b] => .bool <$> (! ·) <$> c.eq a b
  | "-.", [a] => do pure (.int (- (← asInt a)))
  | "\\in", [a, S] => .bool <$> c.mem a S
  | "\\notin", [a, S] => .bool <$> (! ·) <$> c.mem a S
  | "\\subseteq", [A, B] => .bool <$> c.subseteq A B
  | "{}", _ => c.mkSet vs
  | "<<>>", _ => pure (tuple vs)
  | "[]", [f, a] => c.app f a
  | "DOMAIN", [f] => domain f
  | "\\cup", [A, B] => match A, B with
    | .set a, .set b => c.mkSet (a ++ b)
    | _, _ => if A.isSet && B.isSet then pure (.lazy (.cup A B)) else undef "\\cup of a value that is not a set"
  | "\\cap", [A, B] => match A, B with
    | .set a, _ => do c.mkSet (← a.filterM (c.mem · B))
    | _, .set b => do c.mkSet (← b.filterM (c.mem · A))
    | _, _ => if A.isSet && B.isSet then pure (.lazy (.diff A (.lazy (.diff A B))))
              else undef "\\cap of a value that is not a set"
  | "\\", [A, B] => match A with
    | .set a => do if !B.isSet then undef "\\ of a value that is not a set" else c.mkSet (← a.filterM fun v => (! ·) <$> c.mem v B)
    | _ => if A.isSet && B.isSet then pure (.lazy (.diff A B)) else undef "\\ of a value that is not a set"
  | "UNION", [S] => do
    let members ← asSet S
    if !members.all Val.isSet then undef "UNION of a set of values that are not sets" else
    match members.mapM (fun m => match m with | .set l => some l | _ => none) with
    | some ls => c.mkSet ls.flatten
    | none => pure (.lazy (.union members))
  | "SUBSET", [S] => match S with
    | .set l => if l.length > 16 then pure (.lazy (.subset S))
                else pure (.set (l.foldr (fun v acc => acc ++ acc.map (fun s => match s with
                  | .set m => .set (v :: m) | s => s)) [.set []]))
    | _ => if S.isSet then pure (.lazy (.subset S)) else undef "SUBSET of a value that is not a set"
  | "\\X", _ => product vs
  | "->", [A, B] => funSet A B
  | "Seq", [S] => match S with
    | .set [] => pure (.set [tuple []])
    | _ => if S.isSet then pure (.lazy (.seq S)) else undef "Seq of a value that is not a set"
  | "Cardinality", [S] => match S with
    | .set l => pure (.int l.length)
    | .lazy s => if s.infinite then undef "the cardinality of an infinite set"
                 else if S.isSet then .int <$> c.O.card c.eq (c.mem · S)
                 else undef "Cardinality of a value that is not a set"
    | _ => undef "Cardinality of a value that is not a set"
  | "IsFiniteSet", [S] => match S with
    | .set _ => pure (.bool true)
    | .lazy s => if s.infinite then pure (.bool false)
                 else if S.isSet then .bool <$> c.O.finite c.eq (c.mem · S)
                 else undef "IsFiniteSet of a value that is not a set"
    | _ => undef "IsFiniteSet of a value that is not a set"
  -- Sequences.
  | "Len", [s] => do pure (.int (← seqArg s).length)
  | "Head", [s] => c.app s (.int 1)
  | "Tail", [s] => do
    match ← seqArg s with
    | [] => undef "Tail of the empty sequence"
    | _ :: rest => pure (tuple rest)
  | "Append", [s, e] => do pure (tuple ((← seqArg s) ++ [e]))
  | "\\o", [s, t] => do pure (tuple ((← seqArg s) ++ (← seqArg t)))
  | "SubSeq", [s, m, n] => do
    let m ← asInt m
    let n ← asInt n
    let _ ← seqArg s
    let k := (1 + n - m).toNat
    tuple <$> (List.range k).mapM fun (i : Nat) => c.app s (.int (i + m))
  -- TLC: d :> e == [x \in {d} |-> e], and f @@ g, f's where both map.
  | ":>", [d, e] => pure (.fcn [(d, e)])
  | "@@", [f, g] => match f, g with
    | .fcn a, .fcn b => do
      let rest ← b.filterM fun (k, _) => (! ·) <$> anyOf (a.map fun (k', _) => c.eq k k')
      pure (.fcn (a ++ rest))
    | _, _ => if f.isFcn && g.isFcn then unknown "@@ of a function not enumerated"
              else undef "@@ of a value that is not a function"
  | _, [a, b] => match arith o with
    | some f => do f (← asInt a) (← asInt b)
    | none => unknown s!"the operator {o}"
  | _, _ => unknown s!"the operator {o} with {vs.length} arguments"

def op (ρ : Env) : String → List Expr → M Val
  -- IF evaluates only the branch it takes.
  | "IF", [p, a, b] => do c.ev ρ (if ← (c.ev ρ p >>= asBool) then a else b)
  | o, args => do c.strict o (← args.mapM (c.ev ρ))

def eval (ρ : Env) : Expr → M Val
  | .bool b => pure (.bool b)
  | .int n => pure (.int n)
  | .str s => pure (.str s)
  | .name x => match ρ.lookup x with
    | some (.val v) => pure v
    | some (.expr d ρ') => c.ev ρ' d
    | none => constant x
  | .op o args => c.op ρ o args
  | .bind b x s body => do c.binder ρ b x (← c.ev ρ s) body
  | .record fields => do c.mkFcn (← fields.mapM fun (f, e) => do pure (.str f, ← c.ev ρ e))
  | .recordSet fields => do recordSet (← fields.mapM fun (f, e) => do pure (f, ← c.ev ρ e))
  | .except f updates => do
    updates.foldlM (fun v (path, e) => do c.update ρ v (← path.mapM (c.ev ρ)) e) (← c.ev ρ f)
  | .letIn x d body => c.ev ((x, .expr d ρ) :: ρ) body
  | .case arms other => do
    let guards ← arms.mapM fun (p, _) => c.ev ρ p >>= asBool
    let taken := (arms.zip guards).filter (·.2) |>.map (·.1.2)
    match taken, other with
    | [], some e => c.ev ρ e
    | [], none => undef "CASE with no true guard"
    | [e], _ => c.ev ρ e
    | e :: es, _ => do
      -- CASE is a CHOOSE among the values of the true arms.
      let v ← c.ev ρ e
      if ← allOf ((← es.mapM (c.ev ρ)).map (c.eq v)) then pure v
      else unknown "CASE among true arms of different values: that is the choice function's"

/-- `v \in S`. -/
def member (v : Val) : Val → M Bool
  | .set l => anyOf (l.map (c.eq v))
  | .lazy s => match s with
    | .nat => pure (match v with | .int n => n ≥ 0 | _ => false)
    | .int => pure (match v with | .int _ => true | _ => false)
    | .string => pure (match v with | .str _ => true | _ => false)
    | .filter S x p ρ => do
      if !(← c.mem v S) then return false
      c.ev ((x, .val v) :: ρ) p >>= asBool
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
      | .lazy s, .set _ | .set _, .lazy s => if s.infinite then pure false else c.O.same (c.mem · a) (c.mem · b)
      | _, _ => c.O.same (c.mem · a) (c.mem · b)
    else undef "= between values of different kinds"

/-- `f[a]`. -/
def apply (f a : Val) : M Val :=
  match f with
  | .fcn g => do
    for (k, v) in g do
      if ← c.eq a k then return v
    undef "a function applied outside its domain"
  | .lazy (.fcn S x e ρ) => do
    if ← c.mem a S then c.ev ((x, .val a) :: ρ) e
    else undef "a function applied outside its domain"
  | _ => undef "application of a value that is not a function"

end Ctx

def tie (O : Oracle) : Nat → Ctx
  | 0 =>
    let deep {α} : M α := unknown "an expression nested too deep"
    { O, ev := fun _ _ => deep, mem := fun _ _ => deep, eq := fun _ _ => deep, app := fun _ _ => deep }
  | n + 1 =>
    let c := tie O n
    { O, ev := c.eval, mem := c.member, eq := c.equal, app := c.apply }

def sem (O : Oracle) (n : Nat) (ρ : Env) (e : Expr) : M Val := (tie O n).ev ρ e

end Ref
