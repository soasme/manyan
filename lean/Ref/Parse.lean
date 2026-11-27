import Ref.Syntax

/-!
# Reading TLA⁺

Expressions, modules and model configurations. Operators bind as in the
table of precedence in *Specifying Systems* (section 15.2.1); a binder's
body reaches as far right as it can; a junction list (`/\` or `\/` items
aligned in a column) ends at a token in or left of its column.
-/
namespace Ref

inductive Tok where
  | num (n : Nat)
  | str (s : String)
  | id (s : String)
  | sym (s : String)
  deriving BEq, Repr, Inhabited

structure Token where
  tok : Tok
  col : Nat
  deriving Inhabited

/-- Symbols longest first, each with the name the parser knows it by. -/
def symbols : List (String × String) :=
  [("<=>", "<=>"), ("|->", "|->"), ("<<", "<<"), (">>", ">>"), ("==", "=="), ("/\\", "/\\"),
   ("\\/", "\\/"), ("=>", "=>"), ("->", "->"), ("<-", "<-"), ("<=", "<="), ("=<", "<="), (">=", ">="),
   ("/=", "#"), ("..", ".."), (":>", ":>"), ("@@", "@@"), ("[]", "[]"), ("<>", "<>"), ("~>", "~>")]

def words : List (String × String) :=
  [("lnot", "~"), ("neg", "~"), ("land", "/\\"), ("lor", "\\/"), ("leq", "<="), ("geq", ">="),
   ("union", "\\cup"), ("intersect", "\\cap"), ("circ", "\\o"), ("times", "\\X"), ("equiv", "<=>"),
   ("neq", "#")]

partial def tokenize (s : String) : Except String (Array Token) :=
  go s.toList 1 #[]
where
  push (out : Array Token) (t : Tok) (col : Nat) := out.push { tok := t, col }
  go : List Char → Nat → Array Token → Except String (Array Token)
  | [], _, out => pure out
  | '\n' :: cs, _, out => go cs 1 out
  | '\\' :: '*' :: cs, col, out => go (cs.dropWhile (· != '\n')) col out
  | '(' :: '*' :: cs, col, out => comment cs 1 (col + 2) out
  | c :: cs, col, out =>
    let all := c :: cs
    if c.isWhitespace then go cs (col + 1) out
    else if c.isDigit then
      let ds := all.takeWhile Char.isDigit
      go (all.drop ds.length) (col + ds.length) (push out (.num (String.ofList ds).toNat!) col)
    else if c.isAlpha || c == '_' then
      let w := all.takeWhile fun d => d.isAlphanum || d == '_'
      go (all.drop w.length) (col + w.length) (push out (.id (String.ofList w)) col)
    else if c == '"' then str cs [] (col + 1) col out
    else if c == '-' && all.take 4 == ['-', '-', '-', '-'] then
      let n := (all.takeWhile (· == '-')).length
      go (all.drop n) (col + n) (push out (.sym "----") col)
    else if c == '=' && all.take 4 == ['=', '=', '=', '='] then
      let n := (all.takeWhile (· == '=')).length
      go (all.drop n) (col + n) (push out (.sym "====") col)
    else if c == '\\' && (cs.head?.map Char.isAlpha).getD false then
      let w := String.ofList (cs.takeWhile Char.isAlpha)
      let name := (words.lookup w).getD ("\\" ++ w)
      go (cs.drop w.length) (col + 1 + w.length) (push out (.sym name) col)
    else
      let rest := String.ofList all
      match symbols.find? (fun (t, _) => rest.startsWith t) with
      | some (t, name) => go (all.drop t.length) (col + t.length) (push out (.sym name) col)
      | none => go cs (col + 1) (push out (.sym (String.singleton c)) col)
  str : List Char → List Char → Nat → Nat → Array Token → Except String (Array Token)
  | '"' :: cs, acc, col, start, out => go cs (col + 1) (push out (.str (String.ofList acc.reverse)) start)
  | '\\' :: e :: cs, acc, col, start, out =>
    let d := match e with | 'n' => '\n' | 't' => '\t' | 'r' => '\r' | c => c
    str cs (d :: acc) (col + 2) start out
  | c :: cs, acc, col, start, out => str cs (c :: acc) (col + 1) start out
  | [], _, _, _, _ => throw "a string without its closing quote"
  comment : List Char → Nat → Nat → Array Token → Except String (Array Token)
  | '*' :: ')' :: cs, 1, col, out => go cs (col + 2) out
  | '*' :: ')' :: cs, n, col, out => comment cs (n - 1) (col + 2) out
  | '(' :: '*' :: cs, n, col, out => comment cs (n + 1) (col + 2) out
  | '\n' :: cs, n, _, out => comment cs n 1 out
  | _ :: cs, n, col, out => comment cs n (col + 1) out
  | [], _, _, _ => throw "a comment without its closing *)"

/-- Infix operators and their precedence; all associate to the left. -/
def infixes : List (String × Nat) :=
  [("=>", 1), ("<=>", 2), ("~>", 2), ("/\\", 3), ("\\/", 3),
   ("=", 5), ("#", 5), ("<", 5), (">", 5), ("<=", 5), (">=", 5),
   ("\\in", 5), ("\\notin", 5), ("\\subseteq", 5), ("\\subset", 5), ("\\supseteq", 5), ("\\supset", 5),
   ("@@", 6), (":>", 7), ("\\cup", 8), ("\\cap", 8), ("\\", 8), ("..", 9),
   ("+", 10), ("-", 10), ("%", 10), ("\\X", 10), ("*", 13), ("\\div", 13), ("\\o", 13), ("^", 14)]

structure Parser where
  toks : Array Token
  pos : Nat := 0
  /-- The column of the junction list being read: a token in or left of it ends an item. -/
  fence : Nat := 0

abbrev P := StateT Parser (Except String)

def peekToken (k : Nat := 0) : P (Option Token) := do
  let s ← get
  pure s.toks[s.pos + k]?

def peek (k : Nat := 0) : P Tok := do
  let s ← get
  match s.toks[s.pos + k]? with
  | some t => pure (if t.col ≤ s.fence then .sym "end" else t.tok)
  | none => pure (.sym "end")

def next : P Tok := do
  let t ← peek
  modify fun s => { s with pos := s.pos + 1 }
  pure t

def isSym (t : String) : P Bool := return (← peek) == .sym t
def isId (t : String) : P Bool := return (← peek) == .id t

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

/-- `a \supseteq b` is `b \subseteq a`. -/
def infixExpr (o : String) (a b : Expr) : Expr :=
  match o with
  | "\\supseteq" => .op "\\subseteq" [b, a]
  | "\\supset" => .op "\\subset" [b, a]
  | _ => .op o [a, b]

def isSubscript : Tok → Bool
  | .id s => s.startsWith "_"
  | _ => false

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
      | _, _ => infixExpr o lhs rhs
  pure lhs

partial def list (close : String) : P (List Expr) := do
  if ← isSym close then let _ ← next; return []
  let mut out := #[← expr]
  while ← isSym "," do
    let _ ← next
    out := out.push (← expr)
  expect close
  pure out.toList

/-- `x, y \in S, z \in T`, the bounds of a quantifier, and its body. -/
partial def binder (b : Binder) : P Expr := do
  let mut bounds := #[]
  repeat
    let mut names := #[← ident]
    while ← isSym "," do
      let _ ← next
      names := names.push (← ident)
    if ← isSym "\\in" then
      let _ ← next
      let s ← expr 6
      bounds := bounds ++ names.map (·, s)
    else bounds := bounds ++ names.map (·, Expr.name "$any")   -- unbounded
    if !(← isSym ",") then break
    let _ ← next
  expect ":"
  let body ← expr
  pure (bounds.foldr (fun (x, s) e => .bind b x s e) body)

/-- The subscript of `[A]_v`, `<<A>>_v`, `WF_v(A)`. -/
partial def subscript : P Expr := do
  match ← next with
  | .id "_" => primary
  | .id s => pure (.name (s.drop 1).toString)
  | t => throw s!"expected a subscript, not {repr t}"

/-- An aligned list of `/\` or `\/` items, starting at its first bullet. -/
partial def junction (bullet : String) (col : Nat) : P Expr := do
  let saved := (← get).fence
  modify fun s => { s with fence := col }
  let mut items := #[← expr]
  repeat
    let some t ← peekToken | break
    if t.tok != .sym bullet || t.col != col then break
    modify fun s => { s with pos := s.pos + 1 }
    items := items.push (← expr)
  modify fun s => { s with fence := saved }
  pure (items.toList.tail.foldl (fun a b => .op bullet [a, b]) items[0]!)

partial def primary : P Expr := do
  let col := ((← peekToken).map (·.col)).getD 0
  match ← next with
  | .num n => suffix (.int n)
  | .str s => suffix (.str s)
  | .sym "(" => do let e ← expr; expect ")"; suffix e
  | .sym "/\\" => junction "/\\" col
  | .sym "\\/" => junction "\\/" col
  | .sym "-" => pure (.op "-." [← expr 12])
  | .sym "~" => pure (.op "~" [← expr 4])
  | .sym "[]" => pure (.op "[]" [← expr 4])
  | .sym "<>" => pure (.op "<>" [← expr 4])
  | .sym "\\A" => binder .all
  | .sym "\\E" => binder .ex
  | .sym "<<" => do
    let es ← list ">>"
    if isSubscript (← peek) then
      match es with
      | [a] => return .op "<<A>>_" [a, ← subscript]
      | _ => throw "<<A>>_v with more than one action"
    suffix (.op "<<>>" es)
  | .sym "{" => suffix (← braces)
  | .sym "[" => suffix (← brackets)
  | .id "TRUE" => suffix (.bool true)
  | .id "FALSE" => suffix (.bool false)
  | .id "CHOOSE" => binder .choose
  | .id "DOMAIN" => pure (.op "DOMAIN" [← expr 9])
  | .id "SUBSET" => pure (.op "SUBSET" [← expr 8])
  | .id "UNION" => pure (.op "UNION" [← expr 8])
  | .id "ENABLED" => pure (.op "ENABLED" [← expr 16])
  | .id "UNCHANGED" => pure (.op "UNCHANGED" [← expr 16])
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
      if ← isId "OTHER" then
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
    let mut defs := #[]
    while !(← isId "IN") do
      defs := defs.push (← definition)
    expect "IN"
    let body ← expr
    pure (defs.foldr (fun (x, ps, d) e => .letIn x ps d e) body)
  | .id "LAMBDA" => do
    let mut ps := #[← ident]
    while ← isSym "," do
      let _ ← next
      ps := ps.push (← ident)
    expect ":"
    pure (.lambda ps.toList (← expr))
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
  | .id f₀ =>
    let mut f := f₀
    while (← isSym "!") && (match ← peek 1 with | .id _ => true | _ => false) do   -- I!D
      let _ ← next
      f := f ++ "!" ++ (← ident)
    if f.startsWith "WF_" || f.startsWith "SF_" then do
      let v ← if f.length > 3 then pure (.name (f.drop 3).toString) else primary
      expect "("
      let a ← expr
      expect ")"
      return .op (f.take 3).toString [v, a]
    if !(← isSym "(") then return ← suffix (.name f)
    let _ ← next
    let mut args ← list ")"
    -- I(p)!D(q): D of the instance I(p), whose parameters come first.
    while (← isSym "!") && (match ← peek 1 with | .id _ => true | _ => false) do
      let _ ← next
      f := f ++ "!" ++ (← ident)
      if ← isSym "(" then let _ ← next; args := args ++ (← list ")")
    suffix (.op f args)
  | .sym "@" => suffix (.name "@")
  | t => throw s!"unexpected {repr t}"

partial def suffix (e : Expr) : P Expr := do
  if ← isSym "[" then
    let _ ← next
    let args ← list "]"
    suffix (.op "app" [e, match args with | [a] => a | _ => .op "<<>>" args])
  else if ← isSym "." then
    let _ ← next
    suffix (.op "app" [e, .str (← ident)])
  else if ← isSym "'" then
    let _ ← next
    suffix (.op "'" [e])
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

/-- `[a |-> e]`, `[a : S]`, `[x \in S |-> e]`, `[S -> T]`, `[f EXCEPT ...]`
or `[A]_v`. -/
partial def brackets : P Expr := do
  if let .id _ := ← peek then
    if (← peek 1) == .sym "|->" then return .record (← fields "|->")
    if (← peek 1) == .sym ":" then return .recordSet (← fields ":")
  let e ← expr
  if ← isId "EXCEPT" then
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
  if ← isSym "]" then
    let _ ← next
    return .op "[A]_" [e, ← subscript]
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

/-- `(p, Op(_))`, the parameters of a definition. -/
partial def params : P (List String) := do
  expect "("
  let mut ps := #[]
  repeat
    ps := ps.push (← ident)
    if ← isSym "(" then   -- Op(_, _): an operator parameter
      while !(← isSym ")") do let _ ← next
      let _ ← next
    if !(← isSym ",") then break
    let _ ← next
  expect ")"
  pure ps.toList

/-- `F == e`, `F(p, Op(_)) == e` or `f[x \in S] == e`. -/
partial def definition : P (String × List String × Expr) := do
  let f ← ident
  if ← isSym "(" then
    let ps ← params
    expect "=="
    return (f, ps, ← expr)
  if ← isSym "[" then
    let _ ← next
    let x ← ident
    expect "\\in"
    let s ← expr
    expect "]"
    expect "=="
    -- The function, `$self` in its body, is recursive.
    return (f, [], .bind .recfcn x s (.letIn f [] (.name "$self") (← expr)))
  expect "=="
  pure (f, [], ← expr)
end

def runP {α} (p : P α) (s : String) : Except String α := do
  let toks ← tokenize s
  let (a, st) ← p.run { toks }
  if st.pos < toks.size then throw s!"unexpected {repr toks[st.pos]!.tok}"
  pure a

def parse (s : String) : Except String Expr := runP (expr 0) s

/-! ## Modules and models -/

/-- `name(params) == INSTANCE module WITH x <- e, ...`, `name` empty for
an unnamed one. -/
structure Instance where
  name : String
  params : List String := []
  module : String
  substs : List (String × Expr)

structure Module where
  name : String := ""
  extends_ : List String := []
  instances : List Instance := []
  consts : List String := []
  vars : List String := []
  defs : List (String × List String × Expr) := []
  assumes : List Expr := []

def skipArity : P Unit := do
  if ← isSym "(" then   -- CONSTANT Op(_, _)
    while !(← isSym ")") do let _ ← next
    let _ ← next

def names : P (List String) := do
  let mut out := #[← ident]
  skipArity
  while ← isSym "," do
    let _ ← next
    out := out.push (← ident)
    skipArity
  pure out.toList

def instanceP (name : String) (params : List String := []) : P Instance := do
  expect "INSTANCE"
  let module ← ident
  let mut substs := []
  if ← isId "WITH" then
    let _ ← next
    repeat
      let x ← ident
      expect "<-"
      substs := substs ++ [(x, ← expr)]
      if !(← isSym ",") then break
      let _ ← next
  pure { name, params, module, substs }

/-- Whether `I(p, ...) == INSTANCE` comes next. -/
def instanceAhead : P Bool := do
  if (← peek 1) != .sym "(" then return false
  let mut k := 2
  let mut depth := 1
  while depth > 0 do
    match ← peek k with
    | .sym "(" => depth := depth + 1
    | .sym ")" => depth := depth - 1
    | .sym "end" => return false
    | _ => pure ()
    k := k + 1
  pure ((← peek k) == .sym "==" && (← peek (k + 1)) == .id "INSTANCE")

partial def moduleP : P Module := do
  while !(← isId "MODULE") do let _ ← next
  let _ ← next
  let mut m : Module := { name := ← ident }
  repeat
    match ← peek with
    | .sym "====" | .sym "end" => break
    | .sym "----" => let _ ← next
    | .id "EXTENDS" => let _ ← next; m := { m with extends_ := ← names }
    | .id "CONSTANT" | .id "CONSTANTS" => let _ ← next; m := { m with consts := m.consts ++ (← names) }
    | .id "VARIABLE" | .id "VARIABLES" => let _ ← next; m := { m with vars := m.vars ++ (← names) }
    | .id "ASSUME" | .id "ASSUMPTION" | .id "AXIOM" =>
      let _ ← next
      if (← peek 1) == .sym "==" then let _ ← next; let _ ← next
      m := { m with assumes := m.assumes ++ [← expr] }
    | .id "THEOREM" | .id "LEMMA" | .id "PROPOSITION" | .id "COROLLARY" =>
      let _ ← next
      if (← peek 1) == .sym "==" then let _ ← next; let _ ← next
      let _ ← expr
    | .id "LOCAL" => let _ ← next
    | .id "RECURSIVE" => let _ ← next; let _ ← names
    | .id "INSTANCE" => m := { m with instances := m.instances ++ [← instanceP ""] }
    | _ =>
      if (← peek 1) == .sym "==" && (← peek 2) == .id "INSTANCE" then
        let x ← ident
        expect "=="
        m := { m with instances := m.instances ++ [← instanceP x] }
      else if ← instanceAhead then
        let x ← ident
        let ps ← params
        expect "=="
        m := { m with instances := m.instances ++ [← instanceP x ps] }
      else
        m := { m with defs := m.defs ++ [← definition] }
  pure m

def parseModule (s : String) : Except String Module := do
  let toks ← tokenize s
  let (m, _) ← moduleP.run { toks }
  pure m

/-- A model configuration: what TLC's `.cfg` file says. -/
structure Config where
  init : Option String := none
  next : Option String := none
  spec : Option String := none
  invariants : List String := []
  properties : List String := []
  constraints : List String := []
  actionConstraints : List String := []
  /-- `C = e`, a value whose other names are model values; `C <- D`. -/
  consts : List (String × Expr) := []
  substs : List (String × String) := []
  deadlock : Bool := true
  /-- What the reference does not model: SYMMETRY, VIEW, ... -/
  other : List String := []

def sections : List String :=
  ["INIT", "NEXT", "SPECIFICATION", "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES",
   "CONSTANT", "CONSTANTS", "CONSTRAINT", "CONSTRAINTS", "ACTION_CONSTRAINT", "ACTION_CONSTRAINTS",
   "CHECK_DEADLOCK", "SYMMETRY", "VIEW", "ALIAS", "POSTCONDITION"]

partial def configP : P Config := do
  let mut c : Config := {}
  let mut part := ""
  repeat
    match ← peek with
    | .sym "end" => break
    | .id w =>
      let _ ← next
      if sections.contains w then
        part := w
        if w == "CHECK_DEADLOCK" then c := { c with deadlock := (← ident) == "TRUE" }
        if ["SYMMETRY", "VIEW", "ALIAS", "POSTCONDITION"].contains w then
          let _ ← ident
          c := { c with other := c.other ++ [w] }
        continue
      match part with
      | "INIT" => c := { c with init := some w }
      | "NEXT" => c := { c with next := some w }
      | "SPECIFICATION" => c := { c with spec := some w }
      | "INVARIANT" | "INVARIANTS" => c := { c with invariants := c.invariants ++ [w] }
      | "PROPERTY" | "PROPERTIES" => c := { c with properties := c.properties ++ [w] }
      | "CONSTRAINT" | "CONSTRAINTS" => c := { c with constraints := c.constraints ++ [w] }
      | "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" =>
        c := { c with actionConstraints := c.actionConstraints ++ [w] }
      | "CONSTANT" | "CONSTANTS" =>
        if ← isSym "<-" then
          let _ ← next
          c := { c with substs := c.substs ++ [(w, ← ident)] }
        else
          expect "="
          c := { c with consts := c.consts ++ [(w, ← expr 6)] }
      | _ => throw s!"{w} outside a section of the configuration"
    | t => throw s!"unexpected {repr t} in the configuration"
  pure c

def parseConfig (s : String) : Except String Config := runP configP s

end Ref
