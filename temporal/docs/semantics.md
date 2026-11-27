# Temporal Specification Semantics

This document defines the formal semantics of `temporal` declarations in terms
of TLA⁺ (*Specifying Systems*, Lamport 2002; [The Manyan TLA⁺ Standard](../../docs/standards/tla2.md)).

`temporal` is a purely passive declaration library. Verification tools such as
Manyan analyse Python source annotated with `temporal` according to the
semantics specified here.

---

## 1. Execution Model and Levels

A TLA⁺ specification describes a set of infinite *behaviors*
$\sigma = \langle s_0, s_1, s_2, \dots \rangle$, where each state $s_i$ assigns
values to the specification's state variables.

Every Temporal declaration belongs to one of TLA⁺'s four expression levels:

| Level | Name | Declarations | May reference |
| --- | --- | --- | --- |
| 0 | Constant | `Const[T]`, `Assume` | Constants and constant operators |
| 1 | State | `State[T]`, `Ghost[T]`, `Init`, `Pure[T]`, `Invariant` | Level 0 + current-state variables |
| 2 | Action | `Action[T]`, `ActionInvariant`, `Requires`, `Ensures`, `Modifies`, `Unchanged` | Level 1 + next-state values (`prime` / post-state), `unchanged`, `enabled` |
| 3 | Temporal | `Property`, `Fairness`, `WeakFairness`, `StrongFairness` | Level 2 + `always`, `eventually`, `leads_to`, `weak_fairness`, `strong_fairness` |

A lower-level declaration must not contain higher-level primitives (for
example, `Invariant` must not use `prime` or `eventually`; `Assume` must not
reference `State` variables).

### Passivity

Temporal declarations perform zero runtime validation and zero automatic
evaluation:

- Importing a specification, instantiating a class, calling an annotated
  function, or constructing `Where`, `Requires`, `Ensures`, `Refines`, or
  `Model` never invokes user predicates.
- All TLA⁺ expression primitives (`implies`, `iff`, `choose`, `old`, `prime`,
  `unchanged`, `enabled`, `always`, `eventually`, `leads_to`, `weak_fairness`,
  `strong_fairness`) are purely declarative stubs that raise
  `NotImplementedError` if called directly at runtime.
- Standard `typing.get_type_hints(..., include_extras=True)`, `typing.get_origin`,
  and `typing.get_args` expose the raw PEP 593 `Annotated` metadata without
  requiring any custom runtime inspector.

---

## 2. Specification Units and Declaration Forms

A Temporal specification may be declared as:

1. **A class** (ordinary class, `@dataclass`, or `Generic[T]` class).
2. **A behavioural protocol** (`typing.Protocol` or `Protocol[T]`): declares an
   abstract behavioural interface purely at the signature level.
3. **A Python module**: module-level annotations and functions declare constants,
   state variables, assumptions, initial predicates, actions, invariants,
   properties, and fairness.
4. **A standalone function**: annotated with `Pure[T]`, `Where`, `Requires`,
   and/or `Ensures`.

### Signature-Level Predicate Forms

Boolean specification roles (`Assume`, `Init`, `Invariant`, `ActionInvariant`,
`Property`, `Fairness`) may be written in either of two equivalent forms:

1. **Signature attribute form** (no method created on the class):
   ```python
   non_negative: Annotated[Invariant, lambda self: self.balance >= 0]
   ```
   Inside `@dataclass`, wrap with `ClassVar[...]` so `dataclasses` does not
   treat the declaration as an `__init__` field:
   ```python
   non_negative: ClassVar[Annotated[Invariant, lambda self: self.balance >= 0]]
   ```
2. **Callable return-signature form** (useful for multi-line definitions or local
   bindings):
   ```python
   def non_negative(self) -> Invariant:
       return self.balance >= 0
   ```

Both forms carry the exact same `Role` inside PEP 593 `Annotated` metadata and
have identical TLA⁺ semantics.

### Composition and Inheritance

- Subclasses inherit all declarations along Python's Method Resolution Order
  (MRO).
- Conflicting `Role` markers for the same symbol (such as `State[Const[int]]`
  or overriding a `Const` as a `State`) are invalid.
- Generic specifications (`Generic[T]`, `Protocol[T]`) are parameterized by
  type variables whose finite domains may be bound in a `Model`.

---

## 3. Constants and State Variables

### `Const[T]`

Declares a TLA⁺ `CONSTANT`. Its value is fixed throughout a behavior and does
not change across transitions. If a `Model` binds the constant in `constants`,
that binding overrides any Python default value.

### `State[T]`

Declares a TLA⁺ `VARIABLE` representing runtime state of the system. Let
$\text{vars}$ denote the tuple of all `State` and `Ghost` variables of the
specification.

### `Ghost[T]`

Declares an auxiliary (specification-only) TLA⁺ `VARIABLE`, such as a history
or prophecy variable.

- In model checking, `Ghost` variables participate in the state space alongside
  `State` variables and are included in $\text{vars}$.
- In implementation conformance checking, runtime code is not required to store
  or mutate `Ghost` attributes; their transitions are specified declaratively
  via `Init`, `Ensures`, or declarative `Action[bool]` relations.

### Inline Type Refinements (`Where`)

`Where(predicate)` defines the subset type $\{x \in T : \text{predicate}(x)\}$.
When composed with a declaration via `Annotated` (for example
`Positive = Annotated[int, Where(lambda x: x > 0)]`):

| Position | Verification obligation |
| --- | --- |
| `Const[Positive]` | Constant assumption: `ASSUME predicate(c)` |
| `State[Positive]` / `Ghost[Positive]` | State invariant: `[] predicate(v)` |
| Function/action parameter `x: Positive` | Precondition: `predicate(x)` |
| Function/action return `-> Positive` | Postcondition: `predicate(result)` |

Multiple `Where` clauses on one annotation are conjoined.

---

## 4. Assumptions and Initial States

### `Assume`

Each `Assume` declaration contributes a constant-level assumption (`ASSUME P`).
Multiple `Assume` declarations (together with `Where` refinements on `Const`
fields) are conjoined and must hold of the constants bound in a `Model`.

### `Init`

Each `Init` declaration contributes a state predicate on the initial state
$s_0$. Multiple `Init` declarations are conjoined:
$\text{Init} \triangleq \bigwedge_k \text{Init}_k$. If no `Init` is declared on
an executable class, a verifier may derive initial values from `__init__` or
dataclass defaults, or require `Model.init`.

---

## 5. Actions and State Transitions

Each method or function returning `Action[T]` declares an atomic transition
action $A_i$.

### Action Styles

1. **Declarative actions (`Action[bool]`):** The body is a two-state TLA⁺
   action formula over current-state expressions (`self.x`) and next-state
   expressions (`prime(self.x)`), with framing via `unchanged(...)`,
   `Modifies(...)`, or `Unchanged(...)`.
2. **Imperative actions (`Action[None]` or `Action[R]`):** The body is ordinary
   executable Python code mutating `State` attributes and optionally returning
   `R`. Unassigned `State` attributes remain `UNCHANGED`. Attached `Requires`
   clauses act as enabling guards; attached `Ensures`, `Modifies`, and
   `Unchanged` clauses are conformance obligations checked against the body.
3. **Abstract actions (body is `...`, e.g., on a `Protocol`):** The action
   relation is defined solely by its signature: `Requires`, `Ensures`,
   `Modifies`, `Unchanged`, and parameter/return `Where` clauses.

### Next-State Relation

For an action $A_i(p_1: T_1, \dots, p_k: T_k)$ with parameters, its
contribution to the next-state relation is existentially quantified over the
parameters' domains (subject to any `Where` and `Requires` guards):

$$A_i^{\exists} \;\triangleq\; \exists p_1 \in D_1, \dots, p_k \in D_k : \text{Guard}_i(\vec{p}) \land \text{Body}_i(\vec{p})$$

The specification's next-state relation is the disjunction of all actions:

$$\text{Next} \;\triangleq\; \bigvee_{i=1}^{m} A_i^{\exists}$$

Behaviors are stutter-invariant: every step satisfies
$[\text{Next}]_{\text{vars}} \triangleq \text{Next} \lor \text{UNCHANGED}\,\text{vars}$.

### Framing (`Modifies` and `Unchanged`)

Let $V$ be the set of all `State` and `Ghost` variable names of the
specification:

- `Modifies(v1, ..., vk)` asserts $\text{UNCHANGED}\,(V \setminus \{v_1, \dots, v_k\})$.
  Empty `Modifies()` asserts $\text{UNCHANGED}\,V$.
- `Unchanged(u1, ..., uj)` asserts $\text{UNCHANGED}\,\{u_1, \dots, u_j\}$.
- Multiple `Modifies` clauses intersect; any variable in `Unchanged` must
  remain unchanged even if listed in `Modifies`.
- Naming a variable not declared on the specification is a static error.

---

## 6. Function Contracts and Purity

### `Pure[T]`

Declares a side-effect-free operator returning `T` (TLA⁺ Level 0 if it accesses
no state variables; Level 1 if it reads state variables). A `Pure` function must
not mutate state variables and may be referenced inside specifications.

### `Requires` and `Ensures`

- **`Requires(predicate)`**: Precondition or action guard. Parameters of
  `predicate` are bound by name to the enclosing function's parameters (including
  `self` for methods); unused parameters may be omitted. State expressions refer
  to the pre-state.
- **`Ensures(predicate)`**: Postcondition. Parameters of `predicate` are bound
  by name to the enclosing function's parameters, plus `result` for the return
  value (omissible when returning `None` or unconstrained).
  - Inside `Ensures`, `old(expr)` evaluates in the **pre-state** ($s$).
  - Outside `old(...)`, state expressions evaluate in the **post-state** ($s'$).
  - Multiple `Requires` clauses are conjoined; multiple `Ensures` clauses are
    conjoined.

### Pre-State / Post-State Convention Summary

| Context | Bare state expr `self.x` | Explicit partner |
| --- | --- | --- |
| Declarative `Action[bool]` / `ActionInvariant` | Pre-state $x$ | `prime(self.x)` = post-state $x'$ |
| `Requires` | Pre-state $x$ | *(none — single-state)* |
| `Ensures` | Post-state $x'$ | `old(self.x)` = pre-state $x$ |

---

## 7. Invariants, Fairness, and Temporal Properties

### `Invariant`

A state predicate $I$ that must hold in every reachable state:
$\text{Spec} \implies \square I$.

### `ActionInvariant`

A two-state predicate $A$ (using `self.x` and `prime(self.x)`) that must hold on
every non-stuttering step:
$\text{Spec} \implies \square[A]_{\text{vars}}$.

### `Fairness`, `WeakFairness`, and `StrongFairness`

Fairness constraints belong to the **assumption** side of the specification
(left-hand side of $\text{Spec} \implies P$), never to the checked properties:

- `WeakFairness(*vars)` on an action $A$ adds $\text{WF}_v(A)$ where $v$ is
  the tuple of listed variables (or $\text{vars}$ if empty).
- `StrongFairness(*vars)` on an action $A$ adds $\text{SF}_v(A)$ similarly.
- A `Fairness` declaration contributes its temporal fairness formula (built from
  `weak_fairness`, `strong_fairness`, `and`, `all(...)`) to $\text{Fairness}$.

Let $\text{Fairness}$ be the conjunction of all `Fairness` declarations and all
action `WeakFairness` / `StrongFairness` clauses. The complete temporal
specification is:

$$\text{Spec} \;\triangleq\; \text{Init} \;\land\; \square[\text{Next}]_{\text{vars}} \;\land\; \text{Fairness}$$

### `Property`

A general temporal formula $P$ verified against the specification:
$\text{Spec} \implies P$.

---

## 8. Expression Mapping (Python to TLA⁺)

### Native Python Expressions

| Python expression | TLA⁺ equivalent |
| --- | --- |
| `p and q`, `p or q`, `not p` | `p /\ q`, `p \/ q`, `~p` |
| `a == b`, `a != b` | `a = b`, `a # b` |
| `<`, `<=`, `>`, `>=` (including chained `a <= x <= b`) | `<`, `<=`, `>`, `>=` (conjunction for chains) |
| `+`, `-`, `*`, `//`, `%`, `**` | `+`, `-`, `*`, `\div`, `%`, `^` |
| `x in S`, `x not in S` | `x \in S`, `x \notin S` |
| `S \| T`, `S & T`, `S - T`, `S <= T` | `S \cup T`, `S \cap T`, `S \ T`, `S \subseteq T` |
| `all(P(x) for x in S)` | `\A x \in S : P(x)` |
| `any(P(x) for x in S)` | `\E x \in S : P(x)` |
| `{f(x) for x in S}` | `{f(x) : x \in S}` |
| `{x for x in S if P(x)}` | `{x \in S : P(x)}` |
| `{k: f(k) for k in S}` | `[k \in S |-> f(k)]` |
| `{**d, k: v}` | `[d EXCEPT ![k] = v]` |
| `a if cond else b` | `IF cond THEN a ELSE b` |
| `range(a, b)` | `a..(b - 1)` |
| `len(seq)`, `seq[i]` (0-indexed) | `Len(seq)`, `seq[i + 1]` (1-indexed in TLA⁺) |
| `tuple`, `frozenset`, `dict` | Sequence/tuple, Set, Function/Record |

### Temporal Primitives

| Temporal primitive | TLA⁺ equivalent | Level |
| --- | --- | --- |
| `implies(p, q)` | `p => q` | 0–3 |
| `iff(p, q)` | `p <=> q` | 0–3 |
| `choose(S, pred)` | `CHOOSE x \in S : pred(x)` | 0–1 |
| `choose(S)` | `CHOOSE x \in S : TRUE` | 0–1 |
| `prime(e)` | `e'` | 2 |
| `old(e)` | unprimed `e` (within `Ensures`) | 2 |
| `unchanged(e1, ..., ek)` | `UNCHANGED <<e1, ..., ek>>` | 2 |
| `enabled(A)` | `ENABLED A` | 1 (of action `A`) |
| `always(P)` | `[]P` | 3 |
| `eventually(P)` | `<>P` | 3 |
| `leads_to(P, Q)` | `P ~> Q` (`[](P => <>Q)`) | 3 |
| `weak_fairness(A, on=v)` | `WF_v(A)` (`v` defaults to `vars`) | 3 |
| `strong_fairness(A, on=v)` | `SF_v(A)` (`v` defaults to `vars`) | 3 |

---

## 9. Behavioural Protocols and Refinement

A concrete specification $C$ refines an abstract specification (or `Protocol`)
$A$ when every behavior permitted by $C$ maps to a behavior permitted by $A$:

$$C!\text{Spec} \implies \overline{A}!\text{Spec}$$

Refinement is declared in either of two ways:

1. **Identity mapping via inheritance:** `class Concrete(AbstractProtocol): ...`
   maps each abstract variable to the concrete variable of the same name.
2. **Explicit refinement mapping via `Refines[Abstract]`:**
   ```python
   def refines_abstract(self) -> Refines[AbstractProtocol]:
       return Refines(abs_var=expr(self.concrete_var))
   ```
   This corresponds directly to TLA⁺:
   ```tla
   Abs == INSTANCE AbstractProtocol WITH abs_var <- expr(concrete_var)
   Refinement == Abs!Spec
   ```
   and generates the temporal verification obligation `PROPERTY Refinement`.
   An empty `Refines()` specifies the identity mapping without runtime
   inheritance.

---

## 10. Model Configurations

`Model` is the Python counterpart of a TLC / Manyan `.cfg` file:

| `Model` field | TLA⁺ `.cfg` directive | Meaning |
| --- | --- | --- |
| `spec` | Target module | Specification class, protocol, generic alias, or module |
| `constants` | `CONSTANT c = val` | Concrete values or `Symmetry` sets for `Const` declarations |
| `domains` | Finite domain bindings | Finite sets for `TypeVar`s, types (`int`, `ModelValue` sorts), or parameter names |
| `init` | `INIT` | Optional override of initial predicate |
| `actions` | `NEXT` | Optional subset/override of actions (`None` = all; `()` = none) |
| `invariants` | `INVARIANT` | Optional subset/override of invariants (`None` = all; `()` = none) |
| `properties` | `PROPERTY` | Optional subset/override of temporal properties (`None` = all; `()` = none) |
| `state_constraint` | `CONSTRAINT` | State-space bounding predicate |
| `action_constraint` | `ACTION_CONSTRAINT` | Transition bounding predicate |
| `symmetry` | `SYMMETRY` | Explicit symmetry sets (`Permutations(S)`); `Symmetry` values in `constants`/`domains` also declare symmetries |
| `view` | `VIEW` | State projection for equivalence checking |
| `alias` | `ALIAS` | Counterexample trace state transformation |
| `postcondition` | `POSTCONDITION` | Check-wide postcondition evaluated after checking completes |
| `check_deadlock` | `CHECK_DEADLOCK` | Whether terminal states without enabled actions are errors (default `True`) |

### `ModelValue` and `Symmetry`

- `ModelValue(name)` represents an uninterpreted atomic constant. Equality is
  strictly by `(type, name)`; model values are never equal to strings and are
  unordered. Subclassing `ModelValue` creates disjoint uninterpreted sorts
  compatible with Apalache's uninterpreted types.
- `Symmetry(iterable)` is an immutable `frozenset` subclass declaring that all
  permutations of its elements are symmetries of the specification.
