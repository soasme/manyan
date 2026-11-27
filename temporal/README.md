# temporal

Declare behavioural specifications in Python using the semantics of TLA⁺.

Python's standard `typing` module describes the types of values a program accepts
and produces. `temporal` extends that idea to state transitions, invariants,
function contracts, temporal properties, behavioural protocols, and model
configurations—written directly in Python using standard PEP 593 type
annotations and ordinary Python expressions.

```sh
pip install temporal
```

`temporal` is purely a declaration library with **zero third-party dependencies**.
It does not implement a compiler, static analyser, model checker, or runtime
verification engine. Verification is performed externally by tools such as
[Manyan](https://github.com/soasme/manyan):

| Declaration library | Verification tool |
| --- | --- |
| `typing` | mypy, Pyright |
| `temporal` | Manyan |

## Quick start

### Executable state machine with contracts

```python
from dataclasses import dataclass
from typing import Annotated
from temporal import (
    Action, ActionInvariant, Const, Ensures, Ghost, Init, Invariant,
    Model, Modifies, Requires, State, Where, old, prime,
)

Positive = Annotated[int, Where(lambda x: x > 0)]


@dataclass
class BankAccount:
    owner: Const[str]
    balance: State[int] = 0
    ledger: Ghost[tuple[int, ...]] = ()

    def init(self) -> Init:
        return self.balance == 0 and self.ledger == ()

    def non_negative(self) -> Invariant:
        return self.balance >= 0

    def ledger_append_only(self) -> ActionInvariant:
        return len(prime(self.ledger)) >= len(self.ledger)

    def deposit(self, amount: Positive) -> Annotated[
        Action[None],
        Ensures(lambda self, amount: self.balance == old(self.balance) + amount),
        Modifies("balance", "ledger"),
    ]:
        self.balance += amount

    def withdraw(self, amount: Positive) -> Annotated[
        Action[Positive],
        Requires(lambda self, amount: amount <= self.balance),
        Ensures(
            lambda self, amount, result: (
                self.balance == old(self.balance) - amount and result == amount
            )
        ),
        Modifies("balance", "ledger"),
    ]:
        self.balance -= amount
        return amount


model = Model(BankAccount, constants={"owner": "alice"}, domains={int: range(1, 5)})
```

Annotated classes remain ordinary Python:

- They execute natively with zero runtime validation overhead.
- They work with `@dataclass`, `Protocol`, `Generic`, inheritance, and `from __future__ import annotations`.
- They pass `mypy --strict` and `Pyright` because every declaration annotation (`State[T]`, `Const[T]`, `Action[T]`, `Invariant`, ...) is a PEP 593 `Annotated` alias over its underlying Python type.

### Declarative TLA⁺ specification with fairness and liveness

```python
from typing import Annotated, Optional
from temporal import (
    Action, Assume, Const, Fairness, Init, Invariant, Model, ModelValue,
    Property, Requires, State, Symmetry, leads_to, prime, strong_fairness,
    unchanged, weak_fairness,
)


class Proc(ModelValue):
    pass


class Mutex:
    procs: Const[frozenset[Proc]]
    holder: State[Optional[Proc]]
    waiting: State[frozenset[Proc]]

    def non_empty(self) -> Assume:
        return len(self.procs) > 0

    def init(self) -> Init:
        return self.holder is None and self.waiting == frozenset()

    def request(self, p: Proc) -> Annotated[
        Action[bool],
        Requires(lambda self, p: p in self.procs and p not in self.waiting and self.holder != p),
    ]:
        return prime(self.waiting) == (self.waiting | {p}) and unchanged(self.holder)

    def acquire(self, p: Proc) -> Annotated[
        Action[bool],
        Requires(lambda self, p: p in self.waiting and self.holder is None),
    ]:
        return prime(self.holder) == p and prime(self.waiting) == (self.waiting - {p})

    def release(self, p: Proc) -> Annotated[
        Action[bool],
        Requires(lambda self, p: self.holder == p),
    ]:
        return prime(self.holder) is None and unchanged(self.waiting)

    def fair(self) -> Fairness:
        return all(
            strong_fairness(self.acquire(p)) and weak_fairness(self.release(p))
            for p in self.procs
        )

    def starvation_free(self) -> Property:
        return all(leads_to(p in self.waiting, self.holder == p) for p in self.procs)


PROCS = Symmetry({Proc("p1"), Proc("p2"), Proc("p3")})
mutex_model = Model(Mutex, constants={"procs": PROCS}, domains={Proc: PROCS})
```

## API overview

### Declaration annotations (TLA⁺'s four levels)

| Annotation | Underlying type | TLA⁺ level | Meaning |
| --- | --- | --- | --- |
| `Const[T]` | `T` | Constant (0) | `CONSTANT` — fixed across a behavior |
| `Assume` | `bool` | Constant (0) | `ASSUME` — constant assumption |
| `State[T]` | `T` | State (1) | `VARIABLE` — mutable state variable |
| `Ghost[T]` | `T` | State (1) | Auxiliary specification-only variable |
| `Init` | `bool` | State (1) | Initial state predicate |
| `Pure[T]` | `T` | Constant/State (0–1) | Pure side-effect-free operator |
| `Invariant` | `bool` | State (1) | State invariant (`[]I`) |
| `Action[T]` | `T` | Action (2) | Atomic state transition (`Next` disjunct) |
| `ActionInvariant` | `bool` | Action (2) | Two-state action invariant (`[][A]_v`) |
| `Property` | `bool` | Temporal (3) | Temporal property (`PROPERTY`) |
| `Fairness` | `bool` | Temporal (3) | Fairness conjunct (`WF` / `SF`) |

### Contract, framing, fairness, and refinement clauses

- `Where(predicate, description=None)` — refinement predicate `{x \in T : P(x)}`
- `Requires(predicate, description=None)` — function/action precondition or guard
- `Ensures(predicate, description=None)` — function/action postcondition
- `Modifies(*variables)` — frame clause: only listed state variables may change
- `Unchanged(*variables)` — frame clause: listed state variables are `UNCHANGED`
- `WeakFairness(*variables)` — weak fairness metadata on an action (`WF_v(A)`)
- `StrongFairness(*variables)` — strong fairness metadata on an action (`SF_v(A)`)
- `Refines[Spec]` — refinement mapping to an abstract specification (`INSTANCE ... WITH`)

### Expression primitives

- Single-state (executable at runtime): `implies(p, q)`, `iff(p, q)`, `choose(domain, predicate=None)`
- Action-level (declarative only): `old(x)`, `prime(x)`, `unchanged(*xs)`, `enabled(action)`
- Temporal-level (declarative only): `always(p)`, `eventually(p)`, `leads_to(p, q)`, `weak_fairness(action, *, on=None)`, `strong_fairness(action, *, on=None)`

Calling a declarative-only primitive directly at runtime raises `SpecificationError`.

### Model configuration

- `ModelValue(name)` — uninterpreted TLA⁺ model value (subclass for disjoint sorts)
- `Symmetry(iterable)` — `frozenset` subclass marking a `SYMMETRY` set
- `Model(spec, *, constants=..., domains=..., ...)` — immutable `.cfg` declaration

### Passive reflection

- `Role`, `TemporalMetadata`, `FieldInfo`, `ContractInfo`, `SpecInfo`
- `is_temporal_metadata`, `get_metadata`, `get_role`, `strip_temporal`
- `get_contract(func)`, `get_spec(cls_or_module)`

## Documentation and examples

- [Specification Semantics](docs/semantics.md) — formal TLA⁺ semantics of every declaration, operator, contract, refinement, and model configuration.
- [User Guide](docs/guide.md) — patterns for state machines, contracts, protocols, refinement, and model configurations.
- [Examples](examples/) — `die_hard.py`, `bank_account.py`, `bounded_queue.py`, `mutex.py`, `two_phase_commit.py`, `contracts.py`.

## License

MIT; see [LICENSE](LICENSE).
