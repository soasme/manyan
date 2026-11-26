import Ref.Sem
import Ref.Parse

/-!
`ref` reads lines from its input and writes one line for each.

    EXPR           its value, as TLC prints values
    EXPR<TAB>VALUE `same` if EXPR equals VALUE, else `differs: ` and the value

or `undefined: ` (TLA⁺ does not say what EXPR is), `unknown: ` (the
reference cannot compute it) or `error: ` (it does not parse), with why.
-/
open Ref

partial def Ref.Val.show : Val → String
  | .bool b => if b then "TRUE" else "FALSE"
  | .int n => toString n
  | .str s => s!"\"{s}\""
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

def depth : Nat := 1000

def answer (r : M String) : String :=
  match r with
  | .ok s => s
  | .error (.undef why) => s!"undefined: {why}"
  | .error (.unknown why) => s!"unknown: {why}"

def line (s : String) : String :=
  match s.splitOn "\t" with
  | [e, v] =>
    match parse e, parse v with
    | .ok e, .ok v => answer do
      let a ← sem Oracle.exec depth [] e
      let b ← sem Oracle.exec depth [] v
      pure (if ← (tie Oracle.exec depth).eq a b then "same" else s!"differs: {a.show}")
    | .error why, _ | _, .error why => s!"error: {why}"
  | _ => match parse s with
    | .ok e => answer (Val.show <$> sem Oracle.exec depth [] e)
    | .error why => s!"error: {why}"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let s ← stdin.getLine
  if s.isEmpty then return
  stdout.putStrLn (line (s.dropEndWhile (· == '\n')).toString)
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
