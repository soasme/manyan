import Ref.Check

/-!
`ref` reads lines from its input and writes one line for each.

    EXPR           its value, as TLC prints values
    EXPR<TAB>VALUE `same` if EXPR equals VALUE, else `differs: ` and the value

or `undefined: ` (TLA⁺ does not say what EXPR is), `unknown: ` (the
reference cannot compute it) or `error: ` (it does not parse), with why.

`ref model M.tla M.cfg UNIVERSE [TRACE]` writes the verdict of a model,
UNIVERSE the definition of the states its behaviors take:

    states N          the distinct reachable states
    init N            the initial ones
    depth N           the levels of the breadth-first search
    invariant I N     I is violated, first by a state at depth N
    deadlock N        a reachable state at depth N has no next state
    property P holds  or `violated`

TRACE, a behavior Manyan prints, is a line `invariant I`, `deadlock`,
`safety P` (a prefix that violates P) or `property P`, a line for each
state (a record of the variables), and for a property's lasso a line
`loop J`, the state (from 0) the last goes back to; `ref` adds
`trace valid N` or `trace invalid N`, N its states.
-/
open Ref

partial def Ref.Val.show : Val → String
  | .bool b => if b then "TRUE" else "FALSE"
  | .int n => toString n
  | .str s => s!"\"{s}\""
  | .model m => m
  | .set l => "{" ++ ", ".intercalate (l.map Val.show) ++ "}"
  | v@(.fcn g) => match v.seq? with
    | some l => "<<" ++ ", ".intercalate (l.map Val.show) ++ ">>"
    | none =>
      if g.all (fun (k, _) => match k with | .str _ => true | _ => false) then
        "[" ++ ", ".intercalate (g.map fun (k, v) => match k with
          | .str f => s!"{f} |-> {v.show}" | _ => "") ++ "]"
      else "(" ++ " @@ ".intercalate (g.map fun (k, v) => s!"{k.show} :> {v.show}") ++ ")"
  | .lazy s => match s with
    | .nat => "Nat" | .int => "Int" | .string => "STRING"
    | _ => "<a set or function not enumerated>"

def answer (r : M String) : String :=
  match r with
  | .ok s => s
  | .error (.undef why) => s!"undefined: {why}"
  | .error (.unknown why) => s!"unknown: {why}"

def evalE (e : Expr) : M Val := (world .exec {}).ev .empty [] e

def line (s : String) : String :=
  match s.splitOn "\t" with
  | [e, v] =>
    match parse e, parse v with
    | .ok e, .ok v => answer do
      let a ← evalE e
      let b ← evalE v
      pure (if ← (world .exec {}).eq a b then "same" else s!"differs: {a.show}")
    | .error why, _ | _, .error why => s!"error: {why}"
  | _ => match parse s with
    | .ok e => answer (Val.show <$> evalE e)
    | .error why => s!"error: {why}"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let s ← stdin.getLine
  if s.isEmpty then return
  stdout.putStrLn (line (s.dropEndWhile (· == '\n')).toString)
  stdout.flush
  loop stdin stdout

def report (v : Verdict) : String :=
  "\n".intercalate ([s!"states {v.states}", s!"init {v.init}", s!"depth {v.depth}"] ++
    v.invariants.map (fun (x, d) => s!"invariant {x} {d}") ++
    (v.deadlock.map (fun d => [s!"deadlock {d}"])).getD [] ++
    v.properties.map (fun (x, h) => s!"property {x} {if h then "holds" else "violated"}"))

/-- The behavior of a trace file, and what it shows violated. -/
def readTrace (md : Model) (vars : List String) (text : String) :
    M (String × List State × Option Nat × Option Expr) := do
  let lines := (text.splitOn "\n").filter (· != "")
  let some what := lines.head? | undef "an empty trace"
  let mut states := []
  let mut loopTo := none
  for l in lines.tail do
    if l.startsWith "loop " then loopTo := (l.drop 5).toString.toNat?
    else match parse l with
      | .ok e => states := states ++ [← asState vars (← md.c.ev .empty [] e)]
      | .error why => undef s!"a state that does not parse: {why}"
  let prop := match what.splitOn " " with
    | ["property", p] | ["safety", p] => some (Expr.name p)
    | _ => none
  if what.startsWith "safety " then loopTo := some (states.length - 1)
  pure (what, states, loopTo, prop)

/-- Whether the last state of a safety trace violates what it shows. -/
def ends (md : Model) (what : String) (s : State) : M Bool :=
  match what.splitOn " " with
  | ["invariant", x] => do pure !(← holds md.c s none [] (.name x))
  | ["deadlock"] => match md.next with
    | some (n, ρ) => do pure !(← md.univ.anyM fun t => holds md.c s (some t) ρ n)
    | none => pure false
  | _ => pure true

/-- The modules `m` uses that are files beside it, and theirs. -/
partial def uses (dir : System.FilePath) (m : Module) (seen : List Module := []) : IO (List Module) := do
  let mut seen := seen
  for x in m.extends_ ++ m.instances.map (·.module) do
    let path := dir / (x ++ ".tla")
    if seen.any (·.name == x) || !(← path.pathExists) then continue
    match parseModule (← IO.FS.readFile path) with
    | .ok n => seen ← uses dir n (n :: seen)
    | .error why => throw (IO.userError s!"{path}: {why}")
  pure seen

def model (args : List String) : IO UInt32 := do
  let (mPath, cPath, univ, trace) ← match args with
    | [m, c, u] => pure (m, c, u, none)
    | [m, c, u, t] => pure (m, c, u, some t)
    | _ => throw (IO.userError "usage: ref model M.tla M.cfg UNIVERSE [TRACE]")
  let mText ← IO.FS.readFile mPath
  let cText ← IO.FS.readFile cPath
  let tText ← match trace with | some t => some <$> IO.FS.readFile t | none => pure none
  let m ← match parseModule mText with
    | .ok m => pure m
    | .error why => IO.println s!"error: {why}"; return 0
  let mods ← uses ((System.FilePath.mk mPath).parent.getD ".") m
  let out : Except String String := do
    let cfg ← parseConfig cText
    pure <| answer do
      let m ← flatten mods m
      let md ← mkModel m cfg univ
      for a in m.assumes do
        if !(← md.c.ev .empty [] a >>= asBool) then return "assume FALSE"
      let mut text := report (← md.check)
      if let some t := tText then
        let (what, states, loopTo, prop) ← readTrace md m.vars t
        let ok ← md.validate states loopTo prop !(what.startsWith "safety ")
        let last ← match states.getLast? with
          | some s => ends md what s
          | none => pure false
        text := text ++ s!"\ntrace {if ok && last then "valid" else "invalid"} {states.length}"
      pure text
  match out with
  | .ok s => IO.println s
  | .error why => IO.println s!"error: {why}"
  pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "model" :: rest => model rest
  | _ => loop (← IO.getStdin) (← IO.getStdout); pure 0
