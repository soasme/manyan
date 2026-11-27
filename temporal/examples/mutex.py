"""Mutual exclusion with starvation freedom using ModelValue, Symmetry, Fairness, and leads_to."""

from __future__ import annotations

from typing import Annotated, Optional, Protocol

from temporal import (
    Action,
    Assume,
    Constant,
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


class Mutex(Protocol):
    procs: Constant[frozenset[Proc]]
    holder: State[Optional[Proc]]
    waiting: State[frozenset[Proc]]

    non_empty_procs: Annotated[bool, Assume(lambda s: len(s.procs) > 0)]
    init: Annotated[
        bool,
        Init(lambda s: s.holder is None and s.waiting == frozenset()),
    ]
    type_ok: Annotated[
        bool,
        Invariant(
            lambda s: (
                (s.holder is None or s.holder in s.procs)
                and s.waiting <= s.procs
                and implies(s.holder is not None, s.holder not in s.waiting)
            )
        ),
    ]
    never_deadlocks: Annotated[
        bool,
        Invariant(
            lambda s: any(
                enabled(s.request(p)) or enabled(s.acquire(p)) or enabled(s.release(p))
                for p in s.procs
            )
        ),
    ]
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
        Property(
            lambda s: all(leads_to(p in s.waiting, s.holder == p) for p in s.procs)
        ),
    ]

    def request(self, p: Proc) -> Annotated[
        bool,
        Requires(lambda s, p: p in s.procs and p not in s.waiting and s.holder != p),
        Action(lambda s, p: prime(s.waiting) == (s.waiting | {p}) and unchanged(s.holder)),
    ]: ...

    def acquire(self, p: Proc) -> Annotated[
        bool,
        Requires(lambda s, p: p in s.waiting and s.holder is None),
        Action(
            lambda s, p: prime(s.holder) == p and prime(s.waiting) == (s.waiting - {p})
        ),
    ]: ...

    def release(self, p: Proc) -> Annotated[
        bool,
        Requires(lambda s, p: s.holder == p),
        Action(lambda s, p: prime(s.holder) is None and unchanged(s.waiting)),
    ]: ...


PROCS = Symmetry({Proc("p1"), Proc("p2"), Proc("p3")})

mutex_model = Model(
    Mutex,
    constants={"procs": PROCS},
    domains={Proc: PROCS},
)
