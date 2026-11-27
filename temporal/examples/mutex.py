"""Mutual exclusion with starvation freedom using ModelValue, Symmetry, Fairness, and leads_to."""

from __future__ import annotations

from typing import Annotated, Optional

from temporal import (
    Action,
    Assume,
    Const,
    Fairness,
    Init,
    Invariant,
    Model,
    ModelValue,
    Property,
    Requires,
    State,
    Symmetry,
    enabled,
    implies,
    leads_to,
    prime,
    strong_fairness,
    unchanged,
    weak_fairness,
)


class Proc(ModelValue):
    """Uninterpreted process identifier sort."""


class Mutex:
    procs: Const[frozenset[Proc]]
    holder: State[Optional[Proc]]
    waiting: State[frozenset[Proc]]

    non_empty_procs: Annotated[Assume, lambda self: len(self.procs) > 0]
    init: Annotated[Init, lambda self: self.holder is None and self.waiting == frozenset()]
    type_ok: Annotated[
        Invariant,
        lambda self: (
            (self.holder is None or self.holder in self.procs)
            and self.waiting <= self.procs
            and implies(self.holder is not None, self.holder not in self.waiting)
        ),
    ]
    never_deadlocks: Annotated[
        Invariant,
        lambda self: any(
            enabled(self.request(p))
            or enabled(self.acquire(p))
            or enabled(self.release(p))
            for p in self.procs
        ),
    ]
    fair: Annotated[
        Fairness,
        lambda self: all(
            strong_fairness(self.acquire(p)) and weak_fairness(self.release(p))
            for p in self.procs
        ),
    ]
    starvation_free: Annotated[
        Property,
        lambda self: all(leads_to(p in self.waiting, self.holder == p) for p in self.procs),
    ]

    def request(self, p: Proc) -> Annotated[
        Action[bool],
        Requires(
            lambda self, p: p in self.procs and p not in self.waiting and self.holder != p
        ),
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


PROCS = Symmetry({Proc("p1"), Proc("p2"), Proc("p3")})

mutex_model = Model(
    Mutex,
    constants={"procs": PROCS},
    domains={Proc: PROCS},
)
