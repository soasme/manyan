"""DieHard water jug puzzle in declarative and executable Temporal styles.

Mirrors ``examples/DieHard.tla``: measure 4 gallons with a 3-gallon jug and
a 5-gallon jug. Violating ``not_solved`` produces a trace that solves the puzzle.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Annotated, ClassVar

from temporal import Action, Init, Invariant, Model, State, prime, unchanged


class DieHardSpec:
    """Pure declarative TLA+ model using signature-level PEP 593 annotations."""

    small: State[int]
    big: State[int]

    init: Annotated[bool, Init(lambda s: s.small == 0 and s.big == 0)]
    type_ok: Annotated[bool, Invariant(lambda s: 0 <= s.small <= 3 and 0 <= s.big <= 5)]
    not_solved: Annotated[bool, Invariant(lambda s: s.big != 4)]

    fill_small: Annotated[bool, Action(lambda s: prime(s.small) == 3 and unchanged(s.big))]
    fill_big: Annotated[bool, Action(lambda s: prime(s.big) == 5 and unchanged(s.small))]
    empty_small: Annotated[bool, Action(lambda s: prime(s.small) == 0 and unchanged(s.big))]
    empty_big: Annotated[bool, Action(lambda s: prime(s.big) == 0 and unchanged(s.small))]

    def pour_small_to_big(self) -> Annotated[bool, Action()]:
        poured = min(self.small, 5 - self.big)
        return prime(self.small) == self.small - poured and prime(self.big) == self.big + poured

    def pour_big_to_small(self) -> Annotated[bool, Action()]:
        poured = min(self.big, 3 - self.small)
        return prime(self.big) == self.big - poured and prime(self.small) == self.small + poured


@dataclass
class DieHard:
    """Executable Python implementation with signature-level specifications."""

    small: State[int] = 0
    big: State[int] = 0

    init: ClassVar[Annotated[bool, Init(lambda s: s.small == 0 and s.big == 0)]]
    type_ok: ClassVar[
        Annotated[bool, Invariant(lambda s: 0 <= s.small <= 3 and 0 <= s.big <= 5)]
    ]
    not_solved: ClassVar[Annotated[bool, Invariant(lambda s: s.big != 4)]]

    def fill_small(self) -> Annotated[None, Action()]:
        self.small = 3

    def fill_big(self) -> Annotated[None, Action()]:
        self.big = 5

    def empty_small(self) -> Annotated[None, Action()]:
        self.small = 0

    def empty_big(self) -> Annotated[None, Action()]:
        self.big = 0

    def pour_small_to_big(self) -> Annotated[None, Action()]:
        poured = min(self.small, 5 - self.big)
        self.small -= poured
        self.big += poured

    def pour_big_to_small(self) -> Annotated[None, Action()]:
        poured = min(self.big, 3 - self.small)
        self.big -= poured
        self.small += poured


spec_model = Model(DieHardSpec)
impl_model = Model(DieHard)
