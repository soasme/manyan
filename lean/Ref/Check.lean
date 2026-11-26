import Std.Data.HashMap
import Ref.Sem
import Ref.Parse

/-!
# What a model's verdict is

A model is a module, its configuration, and a universe: the states a
behavior may take, a set of records over the variables, named by a
definition of the module. Every behavior of the specification must stay in
it; the reference answers relative to it, and does not model what TLC does
to compute states. Its initial states are those of the universe the
initial predicate holds of; a step is a pair of them the specification's
`[][N]_v` allows. So `ENABLED`, `x' \in S`, `\E` in an action, or a
subscript that leaves a variable out mean what they mean in TLA⁺.

Temporal properties are decided as formulas of linear-time temporal logic
whose atoms are state predicates and actions of a step: the behaviors
of the universe that satisfy the specification and violate the property
are the accepted runs of a tableau's product with the state graph, empty
or not (a reachable cycle that fulfils every `<>`).
-/
namespace Ref

def fuel : Nat := 2000

def world (O : Oracle) (w : World) : Ctx := tie O w fuel

/-- The names an expression mentions. -/
partial def Expr.names : Expr → List String
  | .name x => [x]
  | .op _ args => args.flatMap Expr.names
  | .bind _ _ s b => s.names ++ b.names
  | .lambda _ b => b.names
  | .record fs | .recordSet fs => fs.flatMap (·.2.names)
  | .except f us => f.names ++ us.flatMap fun (p, e) => p.flatMap Expr.names ++ e.names
  | .letIn _ _ d b => d.names ++ b.names
  | .case arms o => arms.flatMap (fun (p, e) => p.names ++ e.names) ++ (o.map Expr.names).getD []
  | _ => []

/-- A state as a key: the evaluator keeps each value one way
(`Ref/Canon.lean`), so equal finite states have the same key. -/
def stateKey (s : State) : List (List Int) := s.map (·.2.enc)

def asState (vars : List String) (v : Val) : M State :=
  match v with
  | .fcn g => vars.mapM fun x => match g.find? (fun (k, _) => match k with | .str f => f == x | _ => false) with
    | some (_, v) => pure (x, v)
    | none => undef s!"a state without the variable {x}"
  | _ => undef "a state that is not a record of the variables"

/-- `e` with each free name `x` that `f` renames, `f x`. -/
partial def Expr.rename (f : String → Option String) (bound : List String := []) : Expr → Expr
  | .name x => .name (if bound.contains x then x else (f x).getD x)
  | .op o args => .op (if bound.contains o then o else (f o).getD o) (args.map (·.rename f bound))
  | .bind b x s body => .bind b x (s.rename f bound) (body.rename f (x :: bound))
  | .lambda ps body => .lambda ps (body.rename f (ps ++ bound))
  | .record fs => .record (fs.map fun (k, e) => (k, e.rename f bound))
  | .recordSet fs => .recordSet (fs.map fun (k, e) => (k, e.rename f bound))
  | .except g us => .except (g.rename f bound) (us.map fun (p, e) => (p.map (·.rename f bound), e.rename f bound))
  | .letIn x ps d body => .letIn x ps (d.rename f (ps ++ bound)) (body.rename f (x :: bound))
  | .case arms o => .case (arms.map fun (p, e) => (p.rename f bound, e.rename f bound)) (o.map (·.rename f bound))
  | e => e

/-- A module without instances, `mods` the modules it may use: those it
extends declare its names; an instance `I == INSTANCE N WITH v <- e`
defines `I!D` for each definition `D` of `N`, its variables and constants
`I!v` the expressions substituted for them (by default, the names
themselves). A module not in `mods` is a standard one. -/
partial def flatten (mods : List Module) (m : Module) : M Module := do
  let find (x : String) := mods.find? (·.name == x)
  let mut out : Module := { m with extends_ := [], instances := [], defs := [] }
  for x in m.extends_ do
    if let some e := find x then
      let e ← flatten mods e
      out := { out with consts := e.consts ++ out.consts, vars := e.vars ++ out.vars,
                        defs := out.defs ++ e.defs, assumes := e.assumes ++ out.assumes }
  for i in m.instances do
    let some n := find i.module | undef s!"INSTANCE {i.module}, a module not found"
    let n ← flatten mods n
    let p := if i.name.isEmpty then "" else i.name ++ "!"
    let declared := n.vars ++ n.consts
    let own := declared ++ n.defs.map (·.1)
    let f (x : String) := if own.contains x then some (p ++ x) else none
    let substs := declared.filterMap fun v =>
      let e := (i.substs.lookup v).getD (.name v)
      if p.isEmpty && match e with | .name y => y == v | _ => false then none else some (p ++ v, ([] : List String), e)
    out := { out with defs := out.defs ++ substs ++ n.defs.map fun (d, ps, e) => (p ++ d, ps, e.rename f ps) }
  pure { out with defs := out.defs ++ m.defs }

/-- The names of `e` that nothing in `defs` defines, as the model values
they are in a configuration or a trace. -/
def modelValues (defs : Env) (e : Expr) : Env :=
  (e.names.filter fun n => (defs.lookup n).isNone && !["Nat", "Int", "BOOLEAN", "STRING"].contains n).map
    fun n => (n, .val (.model n))

/-- The world of a module and its configuration: the configuration's
constants and substitutions over the module's definitions; a constant's
names that nothing defines are model values. -/
def mkWorld (m : Module) (cfg : Config) : M World := do
  let defs : Env := m.defs.map fun (x, ps, e) => (x, if ps.isEmpty then .expr e [] else .op ps e [])
  let base : World := { defs, vars := m.vars }
  let c := world .exec base
  let consts ← cfg.consts.mapM fun (x, e) => do pure (x, Def.val (← c.ev .empty (modelValues defs e) e))
  let substs ← cfg.substs.mapM fun (x, y) => match defs.lookup y with
    | some d => pure (x, d)
    | none => undef s!"{x} <- {y}, which nothing defines"
  pure { base with defs := consts ++ substs ++ defs }

/-! ## Linear-time temporal logic -/

inductive Ltl where
  | atom (e : Expr) (ρ : Env) (pos : Bool)  -- a state predicate or action of a step, or its negation
  | tt | ff
  | and (a b : Ltl) | or (a b : Ltl)
  | always (a : Ltl) | eventually (a : Ltl)
  deriving Inhabited

/-- Whether an expression is temporal, its definitions expanded. -/
partial def temporal (c : Ctx) (ρ : Env) (depth : Nat) : Expr → Bool
  | .op o args =>
    ["[]", "<>", "~>", "WF_", "SF_"].contains o || args.any (temporal c ρ depth) ||
    (depth > 0 && match c.lookup ρ o with
      | some (.op _ body ρ') => temporal c ρ' (depth - 1) body
      | _ => false)
  | .name x => depth > 0 && match c.lookup ρ x with
    | some (.expr e ρ') | some (.op [] e ρ') => temporal c ρ' (depth - 1) e
    | _ => false
  | .letIn _ _ d b => temporal c ρ depth d || temporal c ρ depth b
  | .bind _ _ s b => temporal c ρ depth s || temporal c ρ depth b
  | .case arms o => arms.any (fun (p, e) => temporal c ρ depth p || temporal c ρ depth e) ||
      (o.map (temporal c ρ depth)).getD false
  | _ => false

/-- `e` (or `~e`, if not `pos`) in negation normal form. -/
partial def toLtl (c : Ctx) (ρ : Env) (pos : Bool) (e : Expr) : M Ltl := do
  if !temporal c ρ 64 e then return .atom e ρ pos
  let rec_ := toLtl c ρ
  let both (f : Ltl → Ltl → Ltl) (g : Ltl → Ltl → Ltl) (a b : Ltl) := if pos then f a b else g a b
  match e with
  | .op "~" [a] => toLtl c ρ (!pos) a
  | .op "/\\" [a, b] => do pure (both .and .or (← rec_ pos a) (← rec_ pos b))
  | .op "\\/" [a, b] => do pure (both .or .and (← rec_ pos a) (← rec_ pos b))
  | .op "=>" [a, b] => do pure (both .or .and (← rec_ (!pos) a) (← rec_ pos b))
  | .op "<=>" [a, b] => rec_ pos (.op "/\\" [.op "=>" [a, b], .op "=>" [b, a]])
  | .op "[]" [a] => do let x ← rec_ pos a; pure (if pos then .always x else .eventually x)
  | .op "<>" [a] => do let x ← rec_ pos a; pure (if pos then .eventually x else .always x)
  | .op "~>" [a, b] => rec_ pos (.op "[]" [.op "=>" [a, .op "<>" [b]]])
  -- WF_v(A) == <>[](ENABLED <<A>>_v) => []<><<A>>_v; SF_v(A): []<> in place of <>[].
  | .op "WF_" [v, a] => rec_ pos (.op "=>" [.op "<>" [.op "[]" [.op "ENABLED" [.op "<<A>>_" [a, v]]]],
                                          .op "[]" [.op "<>" [.op "<<A>>_" [a, v]]]])
  | .op "SF_" [v, a] => rec_ pos (.op "=>" [.op "[]" [.op "<>" [.op "ENABLED" [.op "<<A>>_" [a, v]]]],
                                          .op "[]" [.op "<>" [.op "<<A>>_" [a, v]]]])
  | .op "IF" [p, a, b] => rec_ pos (.op "\\/" [.op "/\\" [p, a], .op "/\\" [.op "~" [p], b]])
  | .letIn x ps d b => toLtl c ((x, if ps.isEmpty then .expr d ρ else .op ps d ρ) :: ρ) pos b
  | .bind .all x s b | .bind .ex x s b => do
    let quantified := match e with | .bind .all .. => true | _ => false
    let vs ← asSet (← c.ev .empty ρ s)
    let parts ← vs.mapM fun v => toLtl c ((x, .val v) :: ρ) pos b
    let conj := quantified == pos   -- \A, or ~\E
    pure (parts.foldl (fun a p => if conj then .and a p else .or a p) (if conj then .tt else .ff))
  | .name x => match c.lookup ρ x with
    | some (.expr d ρ') | some (.op [] d ρ') => toLtl c ρ' pos d
    | _ => unknown s!"the temporal formula {x}"
  | .op f args => match c.lookup ρ f with
    | some (.op ps body ρ') =>
      if ps.length != args.length then undef s!"{f} applied to {args.length} arguments"
      else toLtl c (ps.zip (args.map (c.arg ρ)) ++ ρ') pos body
    | _ => unknown s!"the temporal operator {f}"
  | _ => unknown "a temporal formula of this form"

/-- A formula's conjuncts. -/
def Ltl.conjuncts : Ltl → List Ltl
  | .and a b => a.conjuncts ++ b.conjuncts
  | .tt => []
  | f => [f]

/-! ## The tableau -/

/-- A formula numbered by its subformulas: `nodes[i]` names its operands
by their numbers. -/
inductive Node where
  | atom (e : Expr) (ρ : Env) (pos : Bool)
  | tt | ff
  | and (a b : Nat) | or (a b : Nat)
  | always (a : Nat) | eventually (a : Nat)
  deriving Inhabited

def number (f : Ltl) : StateM (Array Node) Nat := do
  let n ← match f with
    | .atom e ρ p => pure (Node.atom e ρ p)
    | .tt => pure .tt
    | .ff => pure .ff
    | .and a b => do pure (.and (← number a) (← number b))
    | .or a b => do pure (.or (← number a) (← number b))
    | .always a => do pure (.always (← number a))
    | .eventually a => do pure (.eventually (← number a))
  modifyGet fun ns => (ns.size, ns.push n)

/-- One way a step meets its obligations: the atoms it must satisfy, the
obligations of the next step, and the `<>`s it puts off. -/
structure Way where
  atoms : List Nat
  next : List Nat
  deferred : List Nat

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x == y then y :: ys else y :: insertSorted x ys

/-- The ways to meet the obligations `todo`. -/
partial def expand (ns : Array Node) (todo : List Nat) (w : Way) : List Way :=
  match todo with
  | [] => [w]
  | i :: rest => match ns[i]! with
    | .atom .. => expand ns rest { w with atoms := insertSorted i w.atoms }
    | .tt => expand ns rest w
    | .ff => []
    | .and a b => expand ns (a :: b :: rest) w
    | .or a b => expand ns (a :: rest) w ++ expand ns (b :: rest) w
    | .always a => expand ns (a :: rest) { w with next := insertSorted i w.next }
    | .eventually a => expand ns (a :: rest) w ++
        expand ns rest { w with next := insertSorted i w.next, deferred := insertSorted i w.deferred }

/-- A state graph: `succ[i]` are the states a step from state `i` may go to. -/
structure Graph where
  states : Array State
  init : List Nat
  succ : Array (List Nat)

/-- Whether some behavior of the graph satisfies `f`: a run of the
product reaching a cycle that fulfils every `<>`. -/
def satisfiable (c : Ctx) (g : Graph) (f : Ltl) : M Bool := do
  let (root, ns) := (number f).run #[]
  let eventualities := (List.range ns.size).filter fun i => match ns[i]! with | .eventually _ => true | _ => false
  let mut cache : Std.HashMap (Nat × Nat × Nat) Bool := {}
  -- The product: node (state, obligations), numbered as found.
  let mut ids : Std.HashMap (Nat × List Nat) Nat := {}
  let mut nodes : Array (Nat × List Nat) := #[]
  let mut edges : Array (List (Nat × List Nat)) := #[]  -- (target, deferred)
  for s in g.init do
    if !ids.contains (s, [root]) then
      ids := ids.insert (s, [root]) nodes.size
      nodes := nodes.push (s, [root])
  let mut i := 0
  while i < nodes.size do
    let (s, obl) := nodes[i]!
    let mut out := []
    for w in expand ns obl ⟨[], [], []⟩ do
      for t in g.succ[s]! do
        let mut ok := true
        for a in w.atoms do
          if !ok then break
          let v ← match cache.get? (a, s, t) with
            | some v => pure v
            | none => do
              let .atom e ρ pos := ns[a]! | pure true
              let b ← c.ev (.mk g.states[s]! (some g.states[t]!) false) ρ e >>= asBool
              pure (b == pos)
          cache := cache.insert (a, s, t) v
          ok := v
        if ok then
          let key := (t, w.next)
          let j ← match ids.get? key with
            | some j => pure j
            | none => do
              let j := nodes.size
              ids := ids.insert key j
              nodes := nodes.push key
              pure j
          out := (j, w.deferred) :: out
    edges := edges.push out
    i := i + 1
  -- Tarjan's strongly connected components, iteratively.
  let n := nodes.size
  let mut index : Array (Option Nat) := Array.replicate n none
  let mut low : Array Nat := Array.replicate n 0
  let mut onStack : Array Bool := Array.replicate n false
  let mut stack : List Nat := []
  let mut counter := 0
  let mut comp : Array Nat := Array.replicate n 0
  let mut comps := 0
  for r in List.range n do
    if index[r]!.isSome then continue
    let mut work : List (Nat × List Nat) := [(r, (edges[r]!.map (·.1)))]
    index := index.set! r (some counter); low := low.set! r counter; counter := counter + 1
    stack := r :: stack; onStack := onStack.set! r true
    while !work.isEmpty do
      match work with
      | [] => break
      | (v, todo) :: rest =>
        match todo with
        | u :: more =>
          work := (v, more) :: rest
          match index[u]! with
          | none =>
            index := index.set! u (some counter); low := low.set! u counter; counter := counter + 1
            stack := u :: stack; onStack := onStack.set! u true
            work := (u, edges[u]!.map (·.1)) :: work
          | some iu => if onStack[u]! then low := low.set! v (min low[v]! iu)
        | [] =>
          work := rest
          if low[v]! == index[v]!.get! then
            repeat
              match stack with
              | [] => break
              | w :: st =>
                stack := st; onStack := onStack.set! w false; comp := comp.set! w comps
                if w == v then break
            comps := comps + 1
          match rest with
          | (p, _) :: _ => low := low.set! p (min low[p]! low[v]!)
          | [] => pure ()
  -- A component with an edge inside it, and inside it, for each <>, an edge that does not put it off.
  let mut cyclic : Array Bool := Array.replicate comps false
  let mut fulfilled : Array (List Nat) := Array.replicate comps []
  for v in List.range n do
    for (u, deferred) in edges[v]! do
      if comp[v]! == comp[u]! then
        let k := comp[v]!
        cyclic := cyclic.set! k true
        for e in eventualities do
          if !deferred.contains e && !fulfilled[k]!.contains e then
            fulfilled := fulfilled.set! k (e :: fulfilled[k]!)
  pure ((List.range comps).any fun k => cyclic[k]! && eventualities.all (fulfilled[k]!.contains ·))

/-! ## Checking a model -/

structure Verdict where
  states : Nat
  init : Nat
  depth : Nat
  /-- Each invariant violated, and the least depth of a state violating it. -/
  invariants : List (String × Nat)
  deadlock : Option Nat
  properties : List (String × Bool)

structure Model where
  c : Ctx
  init : List Ltl         -- atoms of the first state
  box : List (Expr × Env) -- actions every step satisfies
  next : Option (Expr × Env)  -- the action whose steps are not a deadlock
  fairness : List Ltl
  invariants : List (String × Expr)
  properties : List (String × Expr)
  constraints : List Expr
  actionConstraints : List Expr
  deadlock : Bool
  univ : List State

def holds (c : Ctx) (s : State) (t : Option State) (ρ : Env) (e : Expr) : M Bool :=
  c.ev (.mk s t false) ρ e >>= asBool

def Ltl.holdsInit (c : Ctx) (s : State) : Ltl → M Bool
  | .atom e ρ pos => do pure ((← holds c s none ρ e) == pos)
  | _ => unknown "a temporal formula about the initial state"

/-- The model a module, its configuration and a universe give. -/
def mkModel (m : Module) (cfg : Config) (univ : String) : M Model := do
  let w ← mkWorld m cfg
  let c0 := world .exec w
  let states ← (← asSet (← c0.ev .empty [] (.name univ))).mapM (asState m.vars)
  let w := { w with states }
  let c := world .exec w
  let vars := Expr.op "<<>>" (m.vars.map .name)
  let (init, box, next, fairness) ← match cfg.spec, cfg.init, cfg.next with
    | some s, _, _ => do
      let parts := (← toLtl c [] true (.name s)).conjuncts
      let mut init := []
      let mut box := []
      let mut nexts := []
      let mut fair := []
      for p in parts do
        match p with
        | .atom .. => init := init ++ [p]
        | .always (.atom e ρ true) =>
          box := box ++ [(e, ρ)]
          if let .op "[A]_" [a, _] := e then nexts := nexts ++ [(a, ρ)]
        | f => fair := fair ++ [f]
      pure (init, box, nexts.head?, fair)
    | none, some i, some n =>
      pure ([Ltl.atom (.name i) [] true], [(Expr.op "[A]_" [.name n, vars], ([] : Env))], some (Expr.name n, ([] : Env)), [])
    | _, _, _ => undef "a configuration without SPECIFICATION or INIT and NEXT"
  pure { c, init, box, next, fairness, deadlock := cfg.deadlock,
         invariants := cfg.invariants.map (fun x => (x, .name x)),
         properties := cfg.properties.map (fun x => (x, .name x)),
         constraints := cfg.constraints.map .name, actionConstraints := cfg.actionConstraints.map .name,
         univ := states }

/-- The states of the universe a step of the specification from `s` may go to. -/
def Model.steps (md : Model) (s : State) : M (List State) :=
  md.univ.filterM fun t => md.box.allM fun (e, ρ) => holds md.c s (some t) ρ e

/-- Whether TLC keeps the state `t`, found by a step from `s` or initial:
its constraints hold of `t`, and its action constraints of the step. -/
def Model.inModel (md : Model) (s : Option State) (t : State) : M Bool := do
  pure ((← md.constraints.allM (holds md.c t none [] ·)) &&
        (← match s with
          | some s => md.actionConstraints.allM (holds md.c s (some t) [] ·)
          | none => pure true))

/-- The reachable states, breadth first, and the depth each is found at;
then the states found by steps outside the constraints, with theirs:
TLC checks each state's invariants as it finds it, and keeps only those
its constraints allow. -/
def Model.explore (md : Model) : M (Graph × Array Nat × List (State × Nat)) := do
  let mut states : Array State := #[]
  let mut ids : Std.HashMap (List (List Int)) Nat := {}
  let mut depth : Array Nat := #[]
  let mut outside : List (State × Nat) := []
  for s in md.univ do
    if !(← md.init.allM (·.holdsInit md.c s)) then continue
    if !(← md.inModel none s) then outside := (s, 1) :: outside; continue
    ids := ids.insert (stateKey s) states.size
    states := states.push s
    depth := depth.push 1
  let init := List.range states.size
  let mut succ : Array (List Nat) := #[]
  let mut i := 0
  while i < states.size do
    let mut out := []
    for t in ← md.steps states[i]! do
      -- TLC's behaviors may always stutter, whatever the action constraints.
      if stateKey t != stateKey states[i]! && !(← md.inModel (some states[i]!) t) then
        outside := (t, depth[i]! + 1) :: outside; continue
      let j ← match ids.get? (stateKey t) with
        | some j => pure j
        | none => do
          let j := states.size
          ids := ids.insert (stateKey t) j
          states := states.push t
          depth := depth.push (depth[i]! + 1)
          pure j
      out := j :: out
    succ := succ.push out.reverse
    i := i + 1
  pure ({ states, init, succ }, depth, outside)

/-- `P` of a property `[]P`, `P` a state predicate. -/
def invariantOf (c : Ctx) (e : Expr) : M (Option (Expr × Env)) := do
  match ← toLtl c [] true e with
  | .always (.atom (.op "[A]_" _) _ _) => pure none
  | .always (.atom p ρ true) => pure (some (p, ρ))
  | _ => pure none

def Model.check (md : Model) : M Verdict := do
  let (g, depth, outside) ← md.explore
  let c := md.c
  let least (ρ : Env) (e : Expr) (among := (List.range g.states.size).map (fun i => (g.states[i]!, depth[i]!)) ++ outside) :
      M (Option Nat) :=
    among.foldlM (init := none) fun l (s, d) => do
      pure (if ← holds c s none ρ e then l else some (min d (l.getD d)))
  let mut invariants := []
  for (x, e) in md.invariants do
    if let some d ← least [] e then invariants := invariants ++ [(x, d)]
  let mut deadlock := none
  if md.deadlock then
    if let some (n, ρ) := md.next then
      for i in List.range g.states.size do
        let s := g.states[i]!
        let moves ← md.univ.anyM fun t => holds c s (some t) ρ n
        if !moves then deadlock := some (min depth[i]! (deadlock.getD depth[i]!))
  let mut properties := []
  for (x, e) in md.properties do
    -- A state outside the constraints TLC finds is no behavior's, but TLC checks []P on it.
    let outsideViolates ← match ← invariantOf c e with
      | some (p, ρ) => do pure (← least ρ p outside).isSome
      | none => pure false
    let violated ← pure outsideViolates <||> satisfiable c g (md.fairness.foldl .and (← toLtl c [] false e))
    properties := properties ++ [(x, !violated)]
  pure { states := g.states.size, init := g.init.length, depth := depth.foldl max 0,
         invariants, deadlock, properties }

/-- Whether a behavior Manyan prints is one of the specification's: its
first state initial, each step allowed, and, for a lasso (the last state
going back to `loop`), one that violates the property `prop`, fair if
`fair` (a prefix that violates a safety property is one stuttering at its
end, which need not be fair). -/
def Model.validate (md : Model) (trace : List State) (loop : Option Nat) (prop : Option Expr)
    (fair : Bool) : M Bool := do
  let some s0 := trace.head? | return false
  for p in md.init do
    if !(← p.holdsInit md.c s0) then return false
  let pairs := trace.zip trace.tail
  for (s, t) in pairs do
    if !((← md.steps s).any (stateKey · == stateKey t)) then return false
  match loop, prop with
  | some j, some e => do
    let n := trace.length
    let last := trace.getLast!
    if !((← md.steps last).any (stateKey · == stateKey trace[j]!)) then return false
    let g : Graph := { states := trace.toArray, init := [0],
                       succ := (List.range n).toArray.map fun i => if i + 1 < n then [i + 1] else [j] }
    satisfiable md.c g ((if fair then md.fairness else []).foldl .and (← toLtl md.c [] false e))
  | _, _ => pure true

end Ref
