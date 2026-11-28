"""Two-Phase Commit protocol specification in Temporal (modeled after Lamport's TwoPhase)."""

from __future__ import annotations

from typing import Annotated, Literal, Protocol

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
    implies,
    leads_to,
    prime,
    unchanged,
    weak_fairness,
)

RMState = Literal["working", "prepared", "committed", "aborted"]
TMState = Literal["init", "committed", "aborted"]


class RM(ModelValue):
    """Uninterpreted resource manager identifier."""


class TwoPhaseCommit(Protocol):
    rms: Constant[frozenset[RM]]
    rm_state: State[dict[RM, RMState]]
    tm_state: State[TMState]
    tm_prepared: State[frozenset[RM]]

    non_empty_rms: Annotated[bool, Assume(lambda s: len(s.rms) > 0)]
    init: Annotated[
        bool,
        Init(
            lambda s: (
                s.rm_state == {r: "working" for r in s.rms}
                and s.tm_state == "init"
                and s.tm_prepared == frozenset()
            )
        ),
    ]
    consistent: Annotated[
        bool,
        Invariant(
            lambda s: all(
                not (s.rm_state[r1] == "committed" and s.rm_state[r2] == "aborted")
                for r1 in s.rms
                for r2 in s.rms
            )
        ),
    ]
    commit_requires_all_prepared: Annotated[
        bool,
        Invariant(
            lambda s: implies(
                s.tm_state == "committed",
                all(s.rm_state[r] in ("prepared", "committed") for r in s.rms),
            )
        ),
    ]
    fair: Annotated[
        bool,
        Fairness(
            lambda s: (
                weak_fairness(s.tm_commit())
                and all(
                    weak_fairness(s.rm_rcv_commit(r))
                    and weak_fairness(s.rm_rcv_abort(r))
                    for r in s.rms
                )
            )
        ),
    ]
    decision_propagates: Annotated[
        bool,
        Property(
            lambda s: leads_to(
                s.tm_state == "committed",
                all(s.rm_state[r] == "committed" for r in s.rms),
            )
        ),
    ]

    def rm_prepare(self, r: RM) -> Annotated[
        bool,
        Requires(lambda s, r: r in s.rms and s.rm_state[r] == "working"),
        Action(
            lambda s, r: (
                prime(s.rm_state) == {**s.rm_state, r: "prepared"}
                and unchanged(s.tm_state, s.tm_prepared)
            )
        ),
    ]: ...

    def tm_rcv_prepared(self, r: RM) -> Annotated[
        bool,
        Requires(
            lambda s, r: (
                r in s.rms and s.tm_state == "init" and s.rm_state[r] == "prepared"
            )
        ),
        Action(
            lambda s, r: (
                prime(s.tm_prepared) == (s.tm_prepared | {r})
                and unchanged(s.rm_state, s.tm_state)
            )
        ),
    ]: ...

    def tm_commit(self) -> Annotated[
        bool,
        Requires(lambda s: s.tm_state == "init" and s.tm_prepared == s.rms),
        Action(
            lambda s: (
                prime(s.tm_state) == "committed"
                and unchanged(s.rm_state, s.tm_prepared)
            )
        ),
    ]: ...

    def tm_abort(self) -> Annotated[
        bool,
        Requires(lambda s: s.tm_state == "init"),
        Action(
            lambda s: (
                prime(s.tm_state) == "aborted"
                and unchanged(s.rm_state, s.tm_prepared)
            )
        ),
    ]: ...

    def rm_rcv_commit(self, r: RM) -> Annotated[
        bool,
        Requires(lambda s, r: r in s.rms and s.tm_state == "committed"),
        Action(
            lambda s, r: (
                prime(s.rm_state) == {**s.rm_state, r: "committed"}
                and unchanged(s.tm_state, s.tm_prepared)
            )
        ),
    ]: ...

    def rm_rcv_abort(self, r: RM) -> Annotated[
        bool,
        Requires(lambda s, r: r in s.rms and s.tm_state == "aborted"),
        Action(
            lambda s, r: (
                prime(s.rm_state) == {**s.rm_state, r: "aborted"}
                and unchanged(s.tm_state, s.tm_prepared)
            )
        ),
    ]: ...


RMS = Symmetry({RM("r1"), RM("r2"), RM("r3")})

two_phase_model = Model(
    TwoPhaseCommit,
    constants={"rms": RMS},
    domains={RM: RMS},
    check_deadlock=False,
)
