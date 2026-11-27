"""Tests for logical, action, and temporal expression primitives."""

from __future__ import annotations

import unittest

from temporal import (
    Invariant,
    SpecificationError,
    State,
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


class TestExecutableLogicalPrimitives(unittest.TestCase):
    def test_implies_truth_table(self) -> None:
        self.assertIs(implies(False, False), True)
        self.assertIs(implies(False, True), True)
        self.assertIs(implies(True, False), False)
        self.assertIs(implies(True, True), True)

    def test_iff_truth_table(self) -> None:
        self.assertIs(iff(False, False), True)
        self.assertIs(iff(False, True), False)
        self.assertIs(iff(True, False), False)
        self.assertIs(iff(True, True), True)

    def test_choose_with_predicate(self) -> None:
        self.assertEqual(choose([1, 2, 3, 4], lambda x: x > 2), 3)
        self.assertEqual(choose(range(10), lambda x: x * x == 49), 7)

    def test_choose_without_predicate(self) -> None:
        self.assertEqual(choose((10, 20, 30)), 10)
        picked = choose(frozenset({"a", "b"}))
        self.assertIn(picked, {"a", "b"})

    def test_choose_short_circuits_generator(self) -> None:
        seen: list[int] = []

        def gen():
            for i in range(10):
                seen.append(i)
                yield i

        self.assertEqual(choose(gen(), lambda x: x == 2), 2)
        self.assertEqual(seen, [0, 1, 2])

    def test_choose_errors(self) -> None:
        with self.assertRaises(ValueError):
            choose(())
        with self.assertRaises(ValueError):
            choose([1, 2, 3], lambda x: x > 10)
        with self.assertRaises(TypeError):
            choose([1, 2], "not callable")  # type: ignore[arg-type]

    def test_single_state_invariant_executable(self) -> None:
        class Lock:
            locked: State[bool] = False
            owner: State[str | None] = None

            def consistent(self) -> Invariant:
                return iff(self.locked, self.owner is not None) and implies(
                    self.owner is not None, self.owner != ""
                )

        lock = Lock()
        self.assertTrue(lock.consistent())
        lock.locked = True
        self.assertFalse(lock.consistent())
        lock.owner = "alice"
        self.assertTrue(lock.consistent())


class TestDeclarativePrimitives(unittest.TestCase):
    def test_spec_only_primitives_raise_specification_error(self) -> None:
        calls = [
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
                with self.assertRaises(SpecificationError) as ctx:
                    thunk()
                self.assertIsInstance(ctx.exception, RuntimeError)
                self.assertIn(f"{name}()", str(ctx.exception))


if __name__ == "__main__":
    unittest.main()
