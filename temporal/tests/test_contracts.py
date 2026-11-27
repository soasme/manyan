"""Tests for contract, framing, fairness, and refinement clauses."""

from __future__ import annotations

import copy
import dataclasses
import pickle
import unittest
from typing import Any

from temporal import (
    Ensures,
    Modifies,
    Refines,
    Requires,
    StrongFairness,
    Unchanged,
    WeakFairness,
    Where,
)


def _boom(*args: Any, **kwargs: Any) -> bool:
    raise AssertionError("Predicate must never be executed by Temporal")


class TestPredicateClauses(unittest.TestCase):
    def test_where_requires_ensures(self) -> None:
        for cls in (Where, Requires, Ensures):
            clause = cls(_boom, "must not run")
            self.assertIs(clause.predicate, _boom)
            self.assertEqual(clause.description, "must not run")
            self.assertEqual(clause, cls(_boom, "must not run"))
            self.assertEqual(hash(clause), hash(cls(_boom, "must not run")))
            self.assertEqual(repr(clause), f"{cls.__name__}({_boom!r}, 'must not run')")
            self.assertEqual(pickle.loads(pickle.dumps(clause)), clause)
            self.assertEqual(copy.deepcopy(clause), clause)

            no_desc = cls(_boom)
            self.assertIsNone(no_desc.description)
            self.assertEqual(repr(no_desc), f"{cls.__name__}({_boom!r})")
            self.assertNotEqual(clause, no_desc)

            with self.assertRaises(dataclasses.FrozenInstanceError):
                clause.description = "mutated"  # type: ignore[misc]

        self.assertNotEqual(Where(_boom), Requires(_boom))
        self.assertNotEqual(Requires(_boom), Ensures(_boom))


class TestVariableClauses(unittest.TestCase):
    def test_modifies_unchanged_fairness(self) -> None:
        for cls in (Modifies, Unchanged, WeakFairness, StrongFairness):
            empty = cls()
            self.assertEqual(empty.variables, ())
            self.assertEqual(repr(empty), f"{cls.__name__}()")

            two = cls("small", "big")
            self.assertEqual(two.variables, ("small", "big"))
            self.assertEqual(repr(two), f"{cls.__name__}('small', 'big')")
            self.assertEqual(two, cls("small", "big"))
            self.assertEqual(hash(two), hash(cls("small", "big")))
            self.assertEqual(pickle.loads(pickle.dumps(two)), two)
            self.assertEqual(copy.deepcopy(two), two)

            with self.assertRaises(dataclasses.FrozenInstanceError):
                two.variables = ()  # type: ignore[misc]

        self.assertNotEqual(Modifies("x"), Unchanged("x"))
        self.assertNotEqual(WeakFairness("x"), StrongFairness("x"))


class TestRefines(unittest.TestCase):
    def test_identity_mapping_pickle_and_immutability(self) -> None:
        empty: Refines[Any] = Refines()
        self.assertEqual(empty.mapping, {})
        self.assertEqual(repr(empty), "Refines()")

        r: Refines[Any] = Refines(capacity=3, items=(1, 2))
        self.assertEqual(r.mapping, {"capacity": 3, "items": (1, 2)})
        self.assertEqual(r, Refines(capacity=3, items=(1, 2)))
        self.assertNotEqual(r, Refines(capacity=4, items=(1, 2)))
        self.assertEqual(repr(r), "Refines(capacity=3, items=(1, 2))")
        self.assertEqual(pickle.loads(pickle.dumps(r)), r)
        self.assertEqual(copy.deepcopy(r), r)

        with self.assertRaises(dataclasses.FrozenInstanceError):
            r.mapping = {}  # type: ignore[misc]


if __name__ == "__main__":
    unittest.main()
