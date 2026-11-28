"""Tests for passive TLA+ expression primitives."""

from __future__ import annotations

import unittest
from collections.abc import Callable

from temporal import (
    always,
    choose,
    enabled,
    eventually,
    iff,
    implies,
    leads_to,
    old,
    prime,
    strong_fairness,
    unchanged,
    weak_fairness,
)


class TestDeclarativePrimitives(unittest.TestCase):
    def test_all_primitives_are_passive_stubs(self) -> None:
        calls: list[tuple[str, Callable[[], object]]] = [
            ("implies", lambda: implies(True, False)),
            ("iff", lambda: iff(True, True)),
            ("choose", lambda: choose([1, 2], lambda x: x > 0)),
            ("choose", lambda: choose([1, 2])),
            ("old", lambda: old(1)),
            ("prime", lambda: prime(1)),
            ("unchanged", lambda: unchanged(1, 2)),
            ("enabled", lambda: enabled(lambda: True)),
            ("always", lambda: always(True)),
            ("eventually", lambda: eventually(True)),
            ("leads_to", lambda: leads_to(True, False)),
            ("weak_fairness", lambda: weak_fairness(lambda: True)),
            ("weak_fairness", lambda: weak_fairness(lambda: True, on=(1,))),
            ("strong_fairness", lambda: strong_fairness(lambda: True)),
            ("strong_fairness", lambda: strong_fairness(lambda: True, on=(1,))),
        ]
        for name, thunk in calls:
            with self.subTest(name=name):
                with self.assertRaises(NotImplementedError) as ctx:
                    thunk()
                self.assertIn(f"{name}()", str(ctx.exception))


if __name__ == "__main__":
    unittest.main()
