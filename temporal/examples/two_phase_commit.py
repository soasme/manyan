"""Two-Phase Commit protocol specification in Temporal (modeled after Lamport's TCommit/TwoPhase)."""

from __future__ import annotations

from typing import Annotated, Literal

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
    eventually,
    implies,
    prime,
    unchanged,
    weak_fairness,
)

RMState = Literal["working", "prepared", "committed", "aborted"]
TMState = Literal["init", "committed", "aborted"]


class RM(ModelValue):
    """Uninterpreted resource manager identifier."""


class TwoPhaseCommit:
    rms: Const[frozenset[RM]]
    rm_state: State[dict[RM, RMState]]
    tm_state: State[TMState]
    tm_prepared: State[frozenset[RM]]

    def non_empty_rms(self) -> Assume:
        return len(self.rms) > 0

    def init(self) -> Init:
        return (
            self.rm_state == {r: "working" for r in self.rms}
            and self.tm_state == "init"
            and self.tm_prepared == frozenset()
        )

    def rm_prepare(self, r: RM) -> Annotated[
        Action[bool],
        Requires(lambda self, r: r in self.rms and self.rm_state[r] == "working"),
    ]:
        return (
            prime(self.rm_state) == {**self.rm_state, r: "prepared"}
            and unchanged(self.tm_state, self.tm_prepared)
        )

    def tm_rcv_prepared(self, r: RM) -> Annotated[
        Action[bool],
        Requires(
            lambda self, r: (
                r in self.rms
                and self.tm_state == "init"
                and self.rm_state[r] == "prepared"
            )
        ),
    ]:
        return (
            prime(self.tm_prepared) == (self.tm_prepared | {r})
            and unchanged(self.rm_state, self.tm_state)
        )

    def tm_commit(self) -> Annotated[
        Action[bool],
        Requires(lambda self: self.tm_state == "init" and self.tm_prepared == self.rms),
    ]:
        return (
            prime(self.tm_state) == "committed"
            and unchanged(self.rm_state, self.tm_prepared)
        )

    def tm_abort(self) -> Annotated[
        Action[bool],
        Requires(lambda self: self.tm_state == "init"),
    ]:
        return (
            prime(self.tm_state) == "aborted"
            and unchanged(self.rm_state, self.tm_prepared)
        )

    def rm_rcv_commit(self, r: RM) -> Annotated[
        Action[bool],
        Requires(lambda self, r: r in self.rms and self.tm_state == "committed"),
    ]:
        return (
            prime(self.rm_state) == {**self.rm_state, r: "committed"}
            and unchanged(self.tm_state, self.tm_prepared)
        )

    def rm_rcv_abort(self, r: RM) -> Annotated[
        Action[bool],
        Requires(lambda self, r: r in self.rms and self.tm_state == "aborted"),
    ]:
        return (
            prime(self.rm_state) == {**self.rm_state, r: "aborted"}
            and unchanged(self.tm_state, self.tm_prepared)
        )

    def consistent(self) -> Invariant:
        """No resource manager commits while another aborts."""
        return all(
            not (self.rm_state[r1] == "committed" and self.rm_state[r2] == "aborted")
            for r1 in self.rms
            for r2 in self.rms
        )

    def commit_requires_all_prepared(self) -> Invariant:
        return implies(
            self.tm_state == "committed",
            all(self.rm_state[r] in ("prepared", "committed") for r in self.rms),
        )

    def fair(self) -> Fairness:
        return (
            weak_fairness(self.tm_commit())
            and all(
                weak_fairness(self.rm_rcv_commit(r))
                and weak_fairness(self.rm_rcv_abort(r))
                for r in self.rms
            )
        )

    def decision_propagates(self) -> Property:
        return implies(
            self.tm_state == "committed",
            eventually(all(self.rm_state[r] == "committed" for r in self.rms)),
        )


RMS = Symmetry({RM("r1"), RM("r2"), RM("r3")})

two_phase_model = Model(
    TwoPhaseCommit,
    constants={"rms": RMS},
    domains={RM: RMS},
    check_deadlock=False,
)
