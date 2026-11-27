# Temporal User Guide

This guide walks through the main patterns for declaring signature-level
behavioural specifications in Python with `temporal`.

## 1. Two Styles of State Machine

`temporal` supports both pure TLA⁺-style models and annotated executable Python
classes using the exact same PEP 593 vocabulary.

### Pure declarative style (`Action[bool]`)

Declare state, initial predicates, and invariants directly in class annotations,
and actions using `prime(...)` and `unchanged(...)`:

```python
from typing import Annotated
from temporal import Action, Init, Invariant, State, prime


class Counter:
    x: State[int]

    init: Annotated[Init, lambda self: self.x == 0]
    bounded: Annotated[Invariant, lambda self: 0 <= self.x <= 10]

    def increment(self) -> Action[bool]:
        return self.x < 10 and prime(self.x) == self.x + 1

    def reset(self) -> Action[bool]:
        return prime(self.x) == 0
```

### Executable implementation style (`Action[None]` / `Action[R]`)

Annotate a normal Python class (including `@dataclass`) so the same file runs in
production and can be verified by Manyan. On a `@dataclass`, wrap predicate
annotations in `ClassVar[...]` so `dataclasses` does not treat them as
`__init__` fields:

```python
from dataclasses import dataclass
from typing import Annotated, ClassVar
from temporal import Action, Init, Invariant, State


@dataclass
class Counter:
    x: State[int] = 0

    init: ClassVar[Annotated[Init, lambda self: self.x == 0]]
    bounded: ClassVar[Annotated[Invariant, lambda self: 0 <= self.x <= 10]]

    def increment(self) -> Action[None]:
        if self.x < 10:
            self.x += 1

    def reset(self) -> Action[None]:
        self.x = 0
```

For multi-line predicates or local bindings, the method-signature form
(`def bounded(self) -> Invariant: ...`) is also equivalent.

## 2. Reusable Refined Types with `Where`

Define domain types once as standard PEP 593 `Annotated` aliases and reuse them
across constants, state variables, parameters, and return types:

```python
from typing import Annotated
from temporal import Const, Pure, State, Where

Positive = Annotated[int, Where(lambda x: x > 0, "positive")]
NonNegative = Annotated[int, Where(lambda x: x >= 0, "non-negative")]


class Wallet:
    limit: Const[Positive]
    balance: State[NonNegative] = 0

    def remaining(self) -> Pure[NonNegative]:
        return self.limit - self.balance
```

Static type checkers treat `Positive` and `NonNegative` as `int`, while
verifiers derive constant assumptions, state invariants, preconditions, and
postconditions automatically from where the alias appears.

## 3. Function Contracts

Attach `Requires`, `Ensures`, `Modifies`, and `Unchanged` to any function or
method using `Annotated` on its return type:

```python
from typing import Annotated
from temporal import Ensures, Pure, Requires


def clamp(value: int, low: int, high: int) -> Annotated[
    Pure[int],
    Requires(lambda low, high: low <= high),
    Ensures(lambda value, low, high, result: low <= result <= high),
]:
    if value < low:
        return low
    if value > high:
        return high
    return value
```

For stateful methods, use `old(...)` inside `Ensures` to refer to pre-state
values while bare `self.attr` refers to post-state values:

```python
def deposit(self, amount: Positive) -> Annotated[
    Action[None],
    Ensures(lambda self, amount: self.balance == old(self.balance) + amount),
    Modifies("balance"),
]:
    self.balance += amount
```

## 4. Behavioural Protocols and Refinement

Use Python's `typing.Protocol` to define a pure signature-level behavioural
interface, and `Refines[Abstract]` to connect a concrete implementation whose
internal state differs from the abstract specification:

```python
from typing import Annotated, Generic, Protocol, TypeVar
from temporal import Action, Ensures, Init, Refines, Requires, State, old

T = TypeVar("T")


class Stack(Protocol[T]):
    items: State[tuple[T, ...]]

    init: Annotated[Init, lambda self: self.items == ()]

    def push(self, item: T) -> Annotated[
        Action[None],
        Ensures(lambda self, item: self.items == old(self.items) + (item,)),
    ]: ...

    def pop(self) -> Annotated[
        Action[T],
        Requires(lambda self: len(self.items) > 0),
        Ensures(lambda self, result: old(self.items) == self.items + (result,)),
    ]: ...


class ArrayStack(Generic[T]):
    _data: State[tuple[T, ...]]

    def __init__(self) -> None:
        self._data = ()

    def as_stack(self) -> Refines[Stack[T]]:
        return Refines(items=self._data)
```

See [examples/bounded_queue.py](../examples/bounded_queue.py) for a full
circular-buffer refinement example.

## 5. Fairness and Liveness Properties

Attach simple per-action fairness directly on the action signature:

```python
def pop(self) -> Annotated[
    Action[T],
    Requires(lambda self: len(self.items) > 0),
    WeakFairness(),
]: ...
```

For parameterized fairness (such as per-process fairness `\A p \in procs : SF_vars(acquire(p))`),
declare a `Fairness` annotation using `weak_fairness` / `strong_fairness`, and
express liveness with `Property` using `always`, `eventually`, and `leads_to`:

```python
fair: Annotated[
    Fairness,
    lambda self: all(strong_fairness(self.acquire(p)) for p in self.procs),
]
starvation_free: Annotated[
    Property,
    lambda self: all(leads_to(p in self.waiting, self.holder == p) for p in self.procs),
]
```

## 6. Configuring Finite Models

Use `Model`, `ModelValue`, and `Symmetry` to declare finite model-checking
configurations alongside your specifications:

```python
from dataclasses import replace
from temporal import Model, ModelValue, Symmetry


class Node(ModelValue):
    pass


NODES = Symmetry({Node("n1"), Node("n2"), Node("n3")})

small_model = Model(
    MyProtocol,
    constants={"nodes": NODES, "max_retries": 2},
    domains={Node: NODES, int: range(3)},
    state_constraint=lambda s: len(s.log) <= 4,
    check_deadlock=True,
)

no_deadlock_model = replace(small_model, check_deadlock=False)
```

## 7. Static Type Checking

`temporal` ships a `py.typed` marker (PEP 561) and passes `mypy --strict` and
`Pyright` (`strict` mode on `temporal` itself). Because every declaration
annotation is a PEP 593 `Annotated` alias:

- `mypy --strict` type-checks all annotated specifications and examples cleanly.
- If you run Pyright in `strict` mode on user specs, prefer named typed
  predicate functions over untyped lambdas inside `Requires`/`Ensures`/`Where`
  to avoid `reportUnknownLambdaType`.
