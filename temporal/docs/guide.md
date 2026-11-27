# Temporal User Guide

This guide walks through the main patterns for declaring signature-level
behavioural specifications in Python with `temporal`.

## 1. Pure Signature-Level vs Executable State Machines

`temporal` uses one uniform set of PEP 593 `Annotated` clauses for both pure
TLA⁺-style models and executable Python classes.

### Pure declarative model

Declare state, initial predicates, actions, and invariants directly in class
annotations:

```python
from typing import Annotated
from temporal import Action, Init, Invariant, State, prime


class Counter:
    x: State[int]

    init: Annotated[bool, Init(lambda s: s.x == 0)]
    bounded: Annotated[bool, Invariant(lambda s: 0 <= s.x <= 10)]

    increment: Annotated[bool, Action(lambda s: s.x < 10 and prime(s.x) == s.x + 1)]
    reset: Annotated[bool, Action(lambda s: prime(s.x) == 0)]
```

### Executable Python class (`@dataclass` or ordinary class)

Attach `Action(...)` directly to real Python methods so the class executes
natively while Manyan verifies conformance against the specification. On a
`@dataclass`, wrap class-level specification annotations in `ClassVar[...]` so
`dataclasses` does not treat them as `__init__` fields:

```python
from dataclasses import dataclass
from typing import Annotated, ClassVar
from temporal import Action, Init, Invariant, Requires, State, prime


@dataclass
class Counter:
    x: State[int] = 0

    init: ClassVar[Annotated[bool, Init(lambda s: s.x == 0)]]
    bounded: ClassVar[Annotated[bool, Invariant(lambda s: 0 <= s.x <= 10)]]

    def increment(self) -> Annotated[
        None,
        Requires(lambda s: s.x < 10),
        Action(lambda s: prime(s.x) == s.x + 1),
    ]:
        self.x += 1

    def reset(self) -> Annotated[None, Action(lambda s: prime(s.x) == 0)]:
        self.x = 0
```

You can also use `Action()` without a predicate when the method body itself
defines the transition, or attach specifications externally to an existing
class:

```python
SafeCounter = Annotated[
    Counter,
    Init(lambda s: s.x == 0),
    Invariant(lambda s: 0 <= s.x <= 10),
]
```

## 2. Reusable Refined Types with `Where`

Define domain types once as standard PEP 593 `Annotated` aliases and reuse them
across constants, state variables, parameters, and return types:

```python
from typing import Annotated
from temporal import Constant, Pure, State, Where

Positive = Annotated[int, Where(lambda x: x > 0, "positive")]
NonNegative = Annotated[int, Where(lambda x: x >= 0, "non-negative")]


class Wallet:
    limit: Constant[Positive]
    balance: State[NonNegative] = 0

    def remaining(self) -> Pure[NonNegative]:
        return self.limit - self.balance
```

## 3. Function Contracts

Attach `Requires`, `Ensures`, `Preserves`, `Modifies`, and `Unchanged` to any
function or method using `Annotated` on its return type:

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

Use `Preserves` when an operation maintains a property whenever it held before
the call (`P(s) => P(s')`), and `old(...)` inside `Ensures` to relate the
return value or post-state to the pre-state.

## 4. Behavioural Protocols and Refinement

Use Python's `typing.Protocol` to define a pure signature-level behavioural
interface, and `Refines[Abstract]` to connect a concrete implementation whose
internal state differs from the abstract specification:

```python
from typing import Annotated, Generic, Protocol, TypeVar
from temporal import Action, Ensures, Init, Refines, Requires, State, old, prime

T = TypeVar("T")


class Stack(Protocol[T]):
    items: State[tuple[T, ...]]

    init: Annotated[bool, Init(lambda s: s.items == ())]

    def push(self, item: T) -> Annotated[
        None,
        Action(lambda s, item: prime(s.items) == s.items + (item,)),
    ]: ...

    def pop(self) -> Annotated[
        T,
        Requires(lambda s: len(s.items) > 0),
        Action(lambda s: prime(s.items) == s.items[:-1]),
        Ensures(lambda s, result: result == old(s.items)[-1]),
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

Attach per-action fairness directly on the action signature:

```python
def release(self) -> Annotated[
    None,
    Requires(lambda s: s.available < s.capacity),
    Action(lambda s: prime(s.available) == s.available + 1),
    WeakFairness(),
]:
    self.available += 1
```

For parameterized fairness (such as per-process fairness `\A p \in procs : SF_vars(acquire(p))`),
declare a `Fairness` annotation using `weak_fairness` / `strong_fairness`, and
express liveness with `Property` using `always`, `eventually`, and `leads_to`:

```python
fair: Annotated[
    bool,
    Fairness(lambda s: all(strong_fairness(s.acquire(p)) for p in s.procs)),
]
starvation_free: Annotated[
    bool,
    Property(lambda s: all(leads_to(p in s.waiting, s.holder == p) for p in s.procs)),
]
```

## 6. Configuring Finite Models

Use `Model`, `Domain`, `ModelValue`, and `Symmetry` to declare finite
model-checking configurations alongside your specifications:

```python
from dataclasses import replace
from temporal import Domain, Model, ModelValue, Symmetry


class Node(ModelValue):
    pass


NODES = Symmetry({Node("n1"), Node("n2"), Node("n3")})

small_model = Model(
    MyProtocol,
    constants={"nodes": NODES, "max_retries": 2},
    domains={Node: NODES, "send.retries": Domain.range(0, 2)},
    state_constraint=lambda s: len(s.log) <= 4,
    check_deadlock=True,
)

no_deadlock_model = replace(small_model, check_deadlock=False)
```

## 7. Static Type Checking

`temporal` ships a `py.typed` marker (PEP 561) and passes `mypy --strict` and
`Pyright` (`strict` mode on `temporal` itself). Because every declaration uses
standard PEP 593 `Annotated` metadata:

- `mypy --strict` type-checks all annotated specifications and examples cleanly.
- If you run Pyright in `strict` mode on user specs, prefer named typed
  predicate functions over untyped lambdas inside clauses to avoid
  `reportUnknownLambdaType`.
