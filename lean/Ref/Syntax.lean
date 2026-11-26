/-!
# The constant expressions of TLA⁺, and their values

An expression is a literal, a name, a built-in operator applied to its
arguments, or one of the forms that bind a name or name fields. Operators
are named as in TLA⁺ (`"\\cup"`, `"Len"`, `"<<>>"` for a tuple, `"{}"` for
an enumerated set, `"[]"` for function application, `"IF"`).

A value is a Boolean, an integer, a string, a finite set, a function with a
finite domain (tuples, sequences and records are functions), or a set or
function the reference keeps unevaluated, as `Nat` or `[x \in Nat |-> x]`.
-/
namespace Ref

inductive Binder where
  | all | ex | choose  -- \A x \in S : P, \E x \in S : P, CHOOSE x \in S : P
  | filter | map       -- {x \in S : P}, {e : x \in S}
  | fcn                -- [x \in S |-> e]
  | select             -- SelectSeq(S, LAMBDA x : P)
  deriving Repr, BEq, Inhabited

inductive Expr where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | name (x : String)
  | op (o : String) (args : List Expr)
  | bind (b : Binder) (x : String) (s body : Expr)
  | record (fields : List (String × Expr))     -- [a |-> e, ...]
  | recordSet (fields : List (String × Expr))  -- [a : S, ...]
  | except (f : Expr) (updates : List (List Expr × Expr))  -- !.a is !["a"]
  | letIn (x : String) (d body : Expr)         -- LET x == d IN body
  | case (arms : List (Expr × Expr)) (other : Option Expr)
  deriving Repr, Inhabited

mutual
inductive Val where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | set (elems : List Val)          -- finite, without duplicates
  | fcn (graph : List (Val × Val))  -- finite domain, without duplicate keys
  | lazy (s : Lazy)
inductive Lazy where
  | nat | int | string
  | filter (s : Val) (x : String) (p : Expr) (ρ : List (String × Def))
  | cup (a b : Val)
  | diff (a b : Val)
  | union (sets : List Val)
  | product (factors : List Val)
  | funSet (dom cod : Val)
  | recordSet (fields : List (String × Val))
  | seq (s : Val)
  | subset (s : Val)
  | fcn (dom : Val) (x : String) (e : Expr) (ρ : List (String × Def))
/-- What a name stands for: a value, or a definition of LET, evaluated
where it is used, as a definition is in TLA⁺. -/
inductive Def where
  | val (v : Val)
  | expr (e : Expr) (ρ : List (String × Def))
end

instance : Inhabited Val := ⟨.bool false⟩

abbrev Env := List (String × Def)

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
