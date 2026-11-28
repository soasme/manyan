# temporal

Declare behavioural specifications in Python using the semantics of TLA⁺.

Python's standard `typing` module describes the types of values that a program
accepts and produces. `temporal` extends that idea to state transitions,
invariants, function contracts, temporal properties, behavioural protocols, and
model configurations—declared directly at the signature level using PEP 593
`Annotated` type annotations and ordinary Python expressions.

```sh
pip install temporal
```

`temporal` is purely a passive declaration library with **zero third-party
dependencies**. It does not implement a compiler, static analyser, runtime
inspector, model checker, or runtime verification engine. Verification is
performed externally by tools such as [Manyan](https://github.com/soasme/manyan):

| Declaration library | Verification tool |
| --- | --- |
| `typing` | mypy, Pyright |
| `temporal` | Manyan |

## Quick start

### Signature-level specifications on an executable class

```python
from dataclasses import dataclass
from typing import Annotated, ClassVar
from temporal import (
    Action, ActionInvariant, Constant, Domain, Ensures, Ghost, Init, Invariant,
    Model, Modifies, Preserves, Requires, State, Where, prime,
)

Positive = Annotated[int, Where(lambda x: x > 0)]


@dataclass
class BankAccount:
    owner: Constant[str]
    balance: State[int] = 0
    ledger: Ghost[tuple[int, ...]] = ()

    init: ClassVar[Annotated[bool, Init(lambda s: s.balance == 0 and s.ledger == ())]]
    non_negative: ClassVar[Annotated[bool, Invariant(lambda s: s.balance >= 0)]]
    ledger_append_only: ClassVar[
        Annotated[bool, ActionInvariant(lambda s: len(prime(s.ledger)) >= len(s.ledger))]
    ]

    def deposit(self, amount: Positive) -> Annotated[
        None,
        Action(
            lambda s, amount: (
                prime(s.balance) == s.balance + amount
                and prime(s.ledger) == s.ledger + (amount,)
            )
        ),
        Preserves(lambda s: s.balance >= 0),
        Modifies("balance", "ledger"),
    ]:
        self.balance += amount

    def withdraw(self, amount: Positive) -> Annotated[
        Positive,
        Requires(lambda s, amount: amount <= s.balance),
        Action(
            lambda s, amount: (
                prime(s.balance) == s.balance - amount
                and prime(s.ledger) == s.ledger + (-amount,)
            )
        ),
        Ensures(lambda s, amount, result: result == amount),
        Modifies("balance", "ledger"),
    ]:
        self.balance -= amount
        return amount


model = Model(
    BankAccount,
    constants={"owner": "alice"},
    domains={
        "deposit.amount": Domain.range(1, 5),
        "withdraw.amount": Domain.range(1, 5),
    },
    state_constraint=lambda s: s.balance <= 10 and len(s.ledger) <= 3,
)
```

Annotated classes remain ordinary Python:

- They execute natively with zero runtime overhead or predicate evaluation.
- Specifications live at the signature level without polluting runtime attributes or methods.
- They work with `@dataclass`, `Protocol`, `Generic`, inheritance, and `from __future__ import annotations`.
- They pass `mypy --strict` and `Pyright` because every declaration uses standard PEP 593 `Annotated` metadata over ordinary Python types.

### Pure signature-level protocol with fairness and liveness

```python
from typing import Annotated, Optional, Protocol
from temporal import (
    Action, Assume, Constant, Fairness, Init, Invariant, Model, ModelValue,
    Property, Requires, State, Symmetry, leads_to, prime, strong_fairness,
    unchanged, weak_fairness,
)


class Proc(ModelValue):
    pass


class Mutex(Protocol):
    procs: Constant[frozenset[Proc]]
    holder: State[Optional[Proc]]
    waiting: State[frozenset[Proc]]

    non_empty: Annotated[bool, Assume(lambda s: len(s.procs) > 0)]
    init: Annotated[bool, Init(lambda s: s.holder is None and s.waiting == frozenset())]
    fair: Annotated[
        bool,
        Fairness(
            lambda s: all(
                strong_fairness(s.acquire(p)) and weak_fairness(s.release(p))
                for p in s.procs
            )
        ),
    ]
    starvation_free: Annotated[
        bool,
        Property(lambda s: all(leads_to(p in s.waiting, s.holder == p) for p in s.procs)),
    ]

    def request(self, p: Proc) -> Annotated[
        bool,
        Requires(lambda s, p: p in s.procs and p not in s.waiting and s.holder != p),
        Action(lambda s, p: prime(s.waiting) == (s.waiting | {p}) and unchanged(s.holder)),
    ]: ...

    def acquire(self, p: Proc) -> Annotated[
        bool,
        Requires(lambda s, p: p in s.waiting and s.holder is None),
        Action(lambda s, p: prime(s.holder) == p and prime(s.waiting) == (s.waiting - {p})),
    ]: ...

    def release(self, p: Proc) -> Annotated[
        bool,
        Requires(lambda s, p: s.holder == p),
        Action(lambda s, p: prime(s.holder) is None and unchanged(s.waiting)),
    ]: ...


PROCS = Symmetry({Proc("p1"), Proc("p2"), Proc("p3")})
mutex_model = Model(Mutex, constants={"procs": PROCS}, domains={Proc: PROCS})
```

## API overview

### Value-level type qualifiers (PEP 593 `Annotated` aliases)

| Annotation | Underlying type | TLA⁺ level | Meaning |
| --- | --- | --- | --- |
| `Constant[T]` | `T` | Constant (0) | `CONSTANT` — fixed across a behavior |
| `State[T]` | `T` | State (1) | `VARIABLE` — mutable state variable |
| `Ghost[T]` | `T` | State (1) | Auxiliary specification-only variable |
| `Pure[T]` | `T` | Constant/State (0–1) | Pure side-effect-free operator |

### Specification, contract, framing, fairness, and refinement clauses

All clauses are frozen metadata dataclasses used inside `Annotated[...]`:

- **System declarations** (optional `predicate` — inline or bound to the annotated method body):
  - `Assume(predicate=None, description=None)` — constant assumption (`ASSUME`)
  - `Init(predicate=None, description=None)` — initial-state predicate (`Init`)
  - `Action(predicate=None, description=None)` — atomic state transition (`Next` disjunct)
  - `Invariant(predicate=None, description=None)` — state invariant (`[]I`)
  - `ActionInvariant(predicate=None, description=None)` — two-state action invariant (`[][A]_v`)
  - `Property(predicate=None, description=None)` — temporal property (`PROPERTY`)
  - `Fairness(predicate=None, description=None)` — fairness assumption (`WF` / `SF`)
- **Contract clauses**:
  - `Where(predicate, description=None)` — refinement type `{x \in T : P(x)}`
  - `Requires(predicate, description=None)` — precondition / action guard
  - `Ensures(predicate, description=None)` — postcondition
  - `Preserves(predicate, description=None)` — inductive preservation (`P(s) => P(s')`)
- **Framing and action fairness**:
  - `Modifies(*variables)` — only listed state variables may change
  - `Unchanged(*variables)` — listed state variables remain `UNCHANGED`
  - `WeakFairness(*variables)` — weak fairness on the annotated action (`WF_v(A)`)
  - `StrongFairness(*variables)` — strong fairness on the annotated action (`SF_v(A)`)
- **Refinement**:
  - `Refines[Spec](**mapping)` — refinement mapping (`INSTANCE Spec WITH ...`)

### Expression primitives (passive TLA⁺ stubs)

- Logical: `implies(p, q)`, `iff(p, q)`, `choose(domain, predicate=None)`
- Action-level: `old(x)`, `prime(x)`, `unchanged(*xs)`, `enabled(action)`
- Temporal-level: `always(p)`, `eventually(p)`, `leads_to(p, q)`, `weak_fairness(action, *, on=None)`, `strong_fairness(action, *, on=None)`

All expression primitives are purely declarative and raise `NotImplementedError` if called directly at runtime.

### Model configuration

- `ModelValue(name)` — uninterpreted TLA⁺ model value (subclass for disjoint sorts)
- `Symmetry(iterable)` — `frozenset` subclass marking a `SYMMETRY` set
- `Domain` — finite domains (`Domain.range(start, stop)` inclusive, `Domain.values(...)`, `Domain.boolean()`)
- `Model(spec, *, constants=..., domains=..., ...)` — frozen `.cfg` declaration

## Documentation and examples

- [Specification Semantics](docs/semantics.md) — formal TLA⁺ semantics of every declaration, contract clause, refinement, expression mapping, and model configuration.
- [User Guide](docs/guide.md) — practical patterns for signature-level specs, contracts, protocols, refinement, and models.
- [Examples](examples/) — `die_hard.py`, `bank_account.py`, `bounded_queue.py`, `mutex.py`, `two_phase_commit.py`, `semaphore.py`, `contracts.py`.

## License

MIT; see [LICENSE](LICENSE).
