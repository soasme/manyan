"""Counting semaphore with explicit action relations, liveness, and weak fairness."""

from __future__ import annotations

from typing import Annotated

from temporal import (
    Action,
    Assume,
    Constant,
    Ensures,
    Init,
    Invariant,
    Model,
    Property,
    Requires,
    State,
    WeakFairness,
    leads_to,
    prime,
)


class Semaphore:
    capacity: Constant[int]
    available: State[int]

    positive_capacity: Annotated[bool, Assume(lambda s: s.capacity > 0)]
    init: Annotated[bool, Init(lambda s: s.available == s.capacity)]
    bounded: Annotated[bool, Invariant(lambda s: 0 <= s.available <= s.capacity)]
    progress: Annotated[
        bool,
        Property(lambda s: leads_to(s.available == 0, s.available > 0)),
    ]

    def __init__(self, capacity: int) -> None:
        self.capacity = capacity
        self.available = capacity

    def acquire(self) -> Annotated[
        bool,
        Requires(lambda s: s.available > 0),
        Action(lambda s: prime(s.available) == s.available - 1),
        Ensures(lambda s, result: result is True),
    ]:
        self.available -= 1
        return True

    def release(self) -> Annotated[
        None,
        Requires(lambda s: s.available < s.capacity),
        Action(lambda s: prime(s.available) == s.available + 1),
        WeakFairness(),
    ]:
        self.available += 1


semaphore_model = Model(
    Semaphore,
    constants={"capacity": 3},
)
