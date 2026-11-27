"""Tests for ModelValue, Symmetry, and Model configuration declarations."""

from __future__ import annotations

import copy
import dataclasses
import pickle
import sys
import unittest
from typing import Generic, TypeVar

from temporal import Action, Const, Init, Invariant, Model, ModelValue, State, Symmetry

T = TypeVar("T")


class Proc(ModelValue):
    pass


class Msg(ModelValue):
    pass


class DummySpec:
    procs: Const[frozenset[Proc]]
    x: State[int] = 0

    def init(self) -> Init:
        return self.x == 0

    def step(self) -> Action[None]:
        self.x += 1

    def non_neg(self) -> Invariant:
        return self.x >= 0


class GenericSpec(Generic[T]):
    item: State[T]


class TestModelValue(unittest.TestCase):
    def test_equality_and_disjoint_sorts(self) -> None:
        a1 = ModelValue("a")
        a2 = ModelValue("a")
        b = ModelValue("b")
        p = Proc("a")
        m = Msg("a")

        self.assertEqual(a1, a2)
        self.assertEqual(hash(a1), hash(a2))
        self.assertNotEqual(a1, b)
        self.assertNotEqual(a1, "a")
        self.assertNotEqual(p, a1)
        self.assertNotEqual(p, m)
        self.assertEqual(p, Proc("a"))
        self.assertEqual(hash(p), hash(Proc("a")))

    def test_unordered_and_immutable(self) -> None:
        p1, p2 = Proc("p1"), Proc("p2")
        with self.assertRaises(TypeError):
            _ = p1 < p2  # type: ignore[operator]
        with self.assertRaises(AttributeError):
            p1.name = "p3"  # type: ignore[misc]
        with self.assertRaises(AttributeError):
            del p1.name  # type: ignore[misc]

    def test_str_repr_and_pickle(self) -> None:
        p = Proc("p1")
        self.assertEqual(str(p), "p1")
        self.assertEqual(repr(p), "Proc('p1')")
        self.assertEqual(pickle.loads(pickle.dumps(p)), p)
        self.assertIs(type(pickle.loads(pickle.dumps(p))), Proc)
        self.assertEqual(copy.copy(p), p)
        self.assertEqual(copy.deepcopy(p), p)

    def test_validation(self) -> None:
        with self.assertRaises(TypeError):
            ModelValue(123)  # type: ignore[arg-type]
        for bad in ("", "   ", "\t\n"):
            with self.assertRaises(ValueError):
                ModelValue(bad)


class TestSymmetry(unittest.TestCase):
    def test_frozenset_semantics_and_identity(self) -> None:
        p1, p2 = Proc("p1"), Proc("p2")
        sym = Symmetry({p1, p2})
        self.assertIsInstance(sym, Symmetry)
        self.assertIsInstance(sym, frozenset)
        self.assertEqual(len(sym), 2)
        self.assertIn(p1, sym)
        self.assertEqual(sym, frozenset({p1, p2}))
        self.assertEqual(hash(sym), hash(frozenset({p1, p2})))
        self.assertEqual(repr(Symmetry()), "Symmetry()")
        self.assertTrue(repr(sym).startswith("Symmetry({"))

        # Set operations return plain frozenset (union need not preserve symmetry).
        combined = sym | frozenset({Proc("p3")})
        self.assertIs(type(combined), frozenset)

        restored = pickle.loads(pickle.dumps(sym))
        self.assertIsInstance(restored, Symmetry)
        self.assertEqual(restored, sym)


class TestModel(unittest.TestCase):
    def test_defaults_and_immutability(self) -> None:
        m = Model(DummySpec)
        self.assertIs(m.spec, DummySpec)
        self.assertEqual(dict(m.constants), {})
        self.assertEqual(dict(m.domains), {})
        self.assertIsNone(m.init)
        self.assertIsNone(m.actions)
        self.assertIsNone(m.invariants)
        self.assertIsNone(m.properties)
        self.assertIsNone(m.state_constraint)
        self.assertIsNone(m.action_constraint)
        self.assertEqual(m.symmetry, ())
        self.assertEqual(m.symmetries, ())
        self.assertIsNone(m.view)
        self.assertIsNone(m.alias)
        self.assertIsNone(m.postcondition)
        self.assertTrue(m.check_deadlock)

        with self.assertRaises(dataclasses.FrozenInstanceError):
            m.check_deadlock = False  # type: ignore[misc]
        with self.assertRaises(TypeError):
            m.constants["x"] = 1  # type: ignore[index]

    def test_constants_domains_and_symmetries(self) -> None:
        procs = Symmetry({Proc("p1"), Proc("p2")})
        msgs = Symmetry({Msg("m1"), Msg("m2")})
        raw_constants = {"procs": procs, "limit": 3}
        raw_domains = {
            Proc: procs,
            Msg: msgs,
            int: range(0, 5),
            str: {"a", "b"},
            "extra": [1, 2, 3],
        }
        m = Model(
            DummySpec,
            constants=raw_constants,
            domains=raw_domains,
            actions=[DummySpec.step],
            invariants=[DummySpec.non_neg],
            properties=(),
            check_deadlock=False,
        )
        # Mutating caller dicts must not affect the Model.
        raw_constants["limit"] = 999
        self.assertEqual(m.constants["limit"], 3)
        self.assertIs(m.domains[Proc], procs)
        self.assertEqual(m.domains[int], range(0, 5))
        self.assertEqual(m.domains[str], frozenset({"a", "b"}))
        self.assertEqual(m.domains["extra"], (1, 2, 3))
        self.assertEqual(m.actions, (DummySpec.step,))
        self.assertEqual(m.invariants, (DummySpec.non_neg,))
        self.assertEqual(m.properties, ())
        self.assertEqual(m.symmetries, (procs, msgs))
        self.assertFalse(m.check_deadlock)

    def test_replace_updates_symmetries_cleanly(self) -> None:
        s1 = Symmetry({Proc("p1"), Proc("p2")})
        s2 = Symmetry({Proc("p1"), Proc("p2"), Proc("p3")})
        m1 = Model(DummySpec, constants={"procs": s1})
        m2 = dataclasses.replace(m1, constants={"procs": s2})
        self.assertEqual(m1.symmetries, (s1,))
        self.assertEqual(m2.symmetries, (s2,))

    def test_accepts_generic_alias_and_module(self) -> None:
        m_generic = Model(GenericSpec[int], domains={int: range(3)})
        self.assertEqual(m_generic.spec, GenericSpec[int])

        this_module = sys.modules[__name__]
        m_mod = Model(this_module, constants={"N": 2})
        self.assertIs(m_mod.spec, this_module)

    def test_passivity(self) -> None:
        def boom(*args: object) -> bool:
            raise AssertionError("Model must never execute predicates")

        m = Model(
            DummySpec,
            init=boom,
            actions=(boom,),
            invariants=(boom,),
            properties=(boom,),
            state_constraint=boom,
            action_constraint=boom,
            view=boom,
            alias=boom,
            postcondition=boom,
        )
        self.assertIs(m.state_constraint, boom)

    def test_validation_errors(self) -> None:
        with self.assertRaises(TypeError):
            Model(DummySpec())  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            Model(123)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            Model(DummySpec, constants=[("a", 1)])  # type: ignore[arg-type]
        with self.assertRaises(ValueError):
            Model(DummySpec, constants={"not valid": 1})
        with self.assertRaises(TypeError):
            Model(DummySpec, domains={int: "abc"})
        with self.assertRaises(TypeError):
            Model(DummySpec, domains={int: 42})  # type: ignore[dict-item]
        with self.assertRaises(TypeError):
            Model(DummySpec, init="Init")  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            Model(DummySpec, invariants=["non_neg"])  # type: ignore[list-item]
        with self.assertRaises(TypeError):
            Model(DummySpec, invariants="non_neg")  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            Model(DummySpec, symmetry=[frozenset({Proc("p1")})])  # type: ignore[list-item]
        with self.assertRaises(TypeError):
            Model(DummySpec, check_deadlock=1)  # type: ignore[arg-type]


if __name__ == "__main__":
    unittest.main()
