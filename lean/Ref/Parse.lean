import Ref.Syntax

/-!
# Reading a constant expression

The expressions of TLA⁺ that `tests/fuzz.py` makes and the values TLC
prints: operators bind as in the table of precedence in *Specifying
Systems* (section 15.2.1); a binder's body reaches as far right as it can.
-/
namespace Ref

inductive Tok where
  | num (n : Nat)
  | str (s : String)
  | id (s : String)
  | sym (s : String)
  deriving BEq, Repr, Inhabited

/-- Symbols longest first, each with the name the parser knows it by. -/
def symbols : List (String × String) :=
  [("<=>", "<=>"), ("|->", "|->"), ("<<", "<<"), (">>", ">>"), ("==", "=="), ("/\\", "/\\"),
   ("\\/", "\\/"), ("=>", "=>"), ("->", "->"), ("<=", "<="), ("=<", "<="), (">=", ">="),
   ("/=", "#"), ("..", ".."), (":>", ":>"), ("@@", "@@"), ("[]", "[]")]

def words : List (String × String) :=
  [("lnot", "~"), ("neg", "~"), ("land", "/\\"), ("lor", "\\/"), ("leq", "<="), ("geq", ">="),
   ("union", "\\cup"), ("intersect", "\\cap"), ("circ", "\\o"), ("times", "\\X")]

partial def tokenize (s : String) : Except String (Array Tok) :=
  go s.toList #[]
where
  go : List Char → Array Tok → Except String (Array Tok)
  | [], out => pure out
  | c :: cs, out =>
    if c.isWhitespace then go cs out
    else if c.isDigit then
      let ds := (c :: cs).takeWhile Char.isDigit
      go ((c :: cs).drop ds.length) (out.push (.num (String.ofList ds).toNat!))
    else if c.isAlpha || c == '_' then
      let w := (c :: cs).takeWhile fun d => d.isAlphanum || d == '_'
      go ((c :: cs).drop w.length) (out.push (.id (String.ofList w)))
    else if c == '"' then str cs [] out
    else if c == '\\' && (cs.head?.map Char.isAlpha).getD false then
      let w := String.ofList (cs.takeWhile Char.isAlpha)
      let name := ((words.lookup w).getD ("\\" ++ w))
      go (cs.drop w.length) (out.push (.sym name))
    else
      let rest := String.ofList (c :: cs)
      match symbols.find? (fun (t, _) => rest.startsWith t) with
      | some (t, name) => go ((c :: cs).drop t.length) (out.push (.sym name))
      | none => go cs (out.push (.sym (String.singleton c)))
  str : List Char → List Char → Array Tok → Except String (Array Tok)
  | '"' :: cs, acc, out => go cs (out.push (.str (String.ofList acc.reverse)))
  | '\\' :: e :: cs, acc, out =>
    let d := match e with | 'n' => '\n' | 't' => '\t' | 'r' => '\r' | c => c
    str cs (d :: acc) out
  | c :: cs, acc, out => str cs (c :: acc) out
  | [], _, _ => throw "a string without its closing quote"

/-- Infix operators and their precedence; all associate to the left. -/
def infixes : List (String × Nat) :=
  [("=>", 1), ("<=>", 2), ("/\\", 3), ("\\/", 3),
   ("=", 5), ("#", 5), ("<", 5), (">", 5), ("<=", 5), (">=", 5),
   ("\\in", 5), ("\\notin", 5), ("\\subseteq", 5),
   ("@@", 6), (":>", 7), ("\\cup", 8), ("\\cap", 8), ("\\", 8), ("..", 9),
   ("+", 10), ("-", 10), ("%", 10), ("\\X", 10), ("*", 13), ("\\div", 13), ("\\o", 13), ("^", 14)]

structure Parser where
  toks : Array Tok
  pos : Nat := 0

abbrev P := StateT Parser (Except String)

def peek (k : Nat := 0) : P Tok := do
  let s ← get
  pure (s.toks[s.pos + k]?.getD (.sym "end"))

def next : P Tok := do
  let t ← peek
  modify fun s => { s with pos := s.pos + 1 }
  pure t

def isSym (t : String) : P Bool := return (← peek) == .sym t

def expect (t : String) : P Unit := do
  let got ← next
  if got != .sym t && got != .id t then throw s!"expected {t}, not {repr got}"

def ident : P String := do
  match ← next with
  | .id x => pure x
  | t => throw s!"expected a name, not {repr t}"

/-- `x \in S`, the bound of a binder. -/
def bound? : Expr → Option (String × Expr)
  | .op "\\in" [.name x, s] => some (x, s)
  | _ => none

mutual
partial def expr (min : Nat := 0) : P Expr := do
  let mut lhs ← primary
  repeat
    let found := match ← peek with
      | .sym o => (infixes.lookup o).map (o, ·)
      | _ => none
    let some (o, prec) := found | break
    if prec < min then break
    let _ ← next
    let rhs ← expr (prec + 1)
    lhs := match o, lhs with
      | "\\X", .op "\\X" fs => .op "\\X" (fs ++ [rhs])  -- A \X B \X C has three factors
      | _, _ => .op o [lhs, rhs]
  pure lhs

partial def list (close : String) : P (List Expr) := do
  if ← isSym close then let _ ← next; return []
  let mut out := #[← expr]
  while ← isSym "," do
    let _ ← next
    out := out.push (← expr)
  expect close
  pure out.toList

partial def binder (b : Binder) : P Expr := do
  let x ← ident
  expect "\\in"
  let s ← expr 6
  expect ":"
  pure (.bind b x s (← expr))

partial def primary : P Expr := do
  match ← next with
  | .num n => suffix (.int n)
  | .str s => suffix (.str s)
  | .sym "(" => do let e ← expr; expect ")"; suffix e
  | .sym "-" => pure (.op "-." [← expr 12])
  | .sym "~" => pure (.op "~" [← expr 4])
  | .sym "\\A" => binder .all
  | .sym "\\E" => binder .ex
  | .sym "<<" => suffix (.op "<<>>" (← list ">>"))
  | .sym "{" => suffix (← braces)
  | .sym "[" => suffix (← brackets)
  | .id "TRUE" => suffix (.bool true)
  | .id "FALSE" => suffix (.bool false)
  | .id "CHOOSE" => binder .choose
  | .id "DOMAIN" => pure (.op "DOMAIN" [← expr 9])
  | .id "SUBSET" => pure (.op "SUBSET" [← expr 8])
  | .id "UNION" => pure (.op "UNION" [← expr 8])
  | .id "IF" => do
    let p ← expr
    expect "THEN"
    let a ← expr
    expect "ELSE"
    pure (.op "IF" [p, a, ← expr])
  | .id "CASE" => do
    let mut arms := #[]
    let mut other := none
    repeat
      if (← peek) == .id "OTHER" then
        let _ ← next
        expect "->"
        other := some (← expr)
        break
      let p ← expr
      expect "->"
      arms := arms.push (p, ← expr)
      if !(← isSym "[]") then break
      let _ ← next
    pure (.case arms.toList other)
  | .id "LET" => do
    let x ← ident
    expect "=="
    let d ← expr
    expect "IN"
    pure (.letIn x d (← expr))
  | .id "SelectSeq" => do
    expect "("
    let s ← expr
    expect ","
    expect "LAMBDA"
    let x ← ident
    expect ":"
    let p ← expr
    expect ")"
    suffix (.bind .select x s p)
  | .id f => if ← isSym "(" then do let _ ← next; suffix (.op f (← list ")")) else suffix (.name f)
  | .sym "@" => suffix (.name "@")
  | t => throw s!"unexpected {repr t}"

partial def suffix (e : Expr) : P Expr := do
  if ← isSym "[" then
    let _ ← next
    let args ← list "]"
    suffix (.op "[]" [e, match args with | [a] => a | _ => .op "<<>>" args])
  else if ← isSym "." then
    let _ ← next
    suffix (.op "[]" [e, .str (← ident)])
  else pure e

/-- `{a, b}`, `{x \in S : P}` or `{e : x \in S}`. -/
partial def braces : P Expr := do
  if ← isSym "}" then let _ ← next; return .op "{}" []
  let e ← expr
  if ← isSym ":" then
    let _ ← next
    match bound? e with
    | some (x, s) => let p ← expr; expect "}"; pure (.bind .filter x s p)
    | none =>
      let x ← ident
      expect "\\in"
      let s ← expr
      expect "}"
      pure (.bind .map x s e)
  else
    let mut out := #[e]
    while ← isSym "," do
      let _ ← next
      out := out.push (← expr)
    expect "}"
    pure (.op "{}" out.toList)

/-- `[a |-> e]`, `[a : S]`, `[x \in S |-> e]`, `[S -> T]` or `[f EXCEPT ...]`. -/
partial def brackets : P Expr := do
  if let .id _ := ← peek then
    if (← peek 1) == .sym "|->" then return .record (← fields "|->")
    if (← peek 1) == .sym ":" then return .recordSet (← fields ":")
  let e ← expr
  if (← peek) == .id "EXCEPT" then
    let _ ← next
    let mut updates := #[]
    repeat
      expect "!"
      let mut path := #[]
      repeat
        if ← isSym "." then
          let _ ← next
          path := path.push (.str (← ident))
        else if ← isSym "[" then
          let _ ← next
          let args ← list "]"
          path := path.push (match args with | [a] => a | _ => .op "<<>>" args)
        else break
      expect "="
      updates := updates.push (path.toList, ← expr)
      if !(← isSym ",") then break
      let _ ← next
    expect "]"
    return .except e updates.toList
  if ← isSym "|->" then
    let _ ← next
    let some (x, s) := bound? e | throw "[e |-> ...] without a bound name"
    let body ← expr
    expect "]"
    return .bind .fcn x s body
  expect "->"
  let t ← expr
  expect "]"
  pure (.op "->" [e, t])

partial def fields (sep : String) : P (List (String × Expr)) := do
  let mut out := #[]
  repeat
    let f ← ident
    expect sep
    out := out.push (f, ← expr)
    if !(← isSym ",") then break
    let _ ← next
  expect "]"
  pure out.toList
end

def parse (s : String) : Except String Expr := do
  let toks ← tokenize s
  let (e, st) ← (expr 0).run { toks }
  if st.pos < toks.size then throw s!"unexpected {repr toks[st.pos]!}"
  pure e

end Ref
