/-!
# The expressions of TLA⁺, and their values

An expression is a literal, a name, an operator applied to its arguments,
or one of the forms that bind a name or name fields. Built-in operators are
named as in TLA⁺ (`"\\cup"`, `"Len"`, `"'"`, `"ENABLED"`, `"[]"`), with
`"<<>>"` for a tuple, `"{}"` for an enumerated set, `"app"` for function
application, `"[A]_"` and `"<<A>>_"` for `[A]_v` and `<<A>>_v`, `"WF_"` and
`"SF_"` (subscript first) for fairness.

A value is a Boolean, an integer, a string, a model value, a finite set, a
function with a finite domain (tuples, sequences and records are
functions), or a set or function the reference keeps unevaluated, as `Nat`
or `[x \in Nat |-> x]`.
-/
namespace Ref

inductive Binder where
  | all | ex | choose  -- \A x \in S : P, \E x \in S : P, CHOOSE x \in S : P
  | filter | map       -- {x \in S : P}, {e : x \in S}
  | fcn                -- [x \in S |-> e]
  | recfcn             -- f[x \in S] == e, which may apply f
  | select             -- SelectSeq(S, LAMBDA x : P)
  deriving Repr, BEq, Inhabited

inductive Expr where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | name (x : String)
  | op (o : String) (args : List Expr)
  | bind (b : Binder) (x : String) (s body : Expr)
  | lambda (params : List String) (body : Expr)
  | record (fields : List (String × Expr))     -- [a |-> e, ...]
  | recordSet (fields : List (String × Expr))  -- [a : S, ...]
  | except (f : Expr) (updates : List (List Expr × Expr))  -- !.a is !["a"]
  | letIn (x : String) (params : List String) (d body : Expr)  -- LET x(params) == d IN body
  | case (arms : List (Expr × Expr)) (other : Option Expr)
  deriving Repr, Inhabited

mutual
inductive Val where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | model (name : String)           -- a model value of the configuration
  | set (elems : List Val)          -- finite, without duplicates
  | fcn (graph : List (Val × Val))  -- finite domain, without duplicate keys
  | lazy (s : Lazy)
inductive Lazy where
  | nat | int | string
  | filter (s : Val) (x : String) (p : Expr) (ρ : List (String × Def)) (σ : St)
  | cup (a b : Val)
  | diff (a b : Val)
  | union (sets : List Val)
  | product (factors : List Val)
  | funSet (dom cod : Val)
  | recordSet (fields : List (String × Val))
  | seq (s : Val)
  | subset (s : Val)
  | fcn (dom : Val) (x : String) (e : Expr) (ρ : List (String × Def)) (σ : St)
/-- What a name stands for: a value, an expression evaluated where it is
used (a definition, or an operator's argument: TLA⁺ substitutes them), or
an operator with parameters. -/
inductive Def where
  | val (v : Val)
  | expr (e : Expr) (ρ : List (String × Def))
  | op (params : List String) (body : Expr) (ρ : List (String × Def))
/-- The states an expression is evaluated in: the variables' values now,
and in the next state for an action, and whether it is under a prime. A
value that keeps an expression to evaluate later keeps its states too. -/
inductive St where
  | mk (cur : List (String × Val)) (nxt : Option (List (String × Val))) (primed : Bool)
end

instance : Inhabited Val := ⟨.bool false⟩

abbrev Env := List (String × Def)
abbrev State := List (String × Val)

def St.empty : St := .mk [] Option.none false
def St.cur : St → State | .mk c _ _ => c
def St.nxt : St → Option State | .mk _ n _ => n
def St.primed : St → Bool | .mk _ _ p => p

/-- Why an expression has no value here. `undef`: TLA⁺ does not say what
the value is (as `<<>>[1]`), so any value is right. `unknown`: TLA⁺ says,
but this reference cannot compute it (as `\A x \in Nat : x >= 0`). -/
inductive Err where
  | undef (why : String)
  | unknown (why : String)
  deriving Repr

abbrev M := Except Err

def undef {α} (why : String) : M α := throw (.undef why)
def unknown {α} (why : String) : M α := throw (.unknown why)

end Ref
