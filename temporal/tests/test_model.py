"""Tests for ModelValue, Symmetry, Domain, and Model configuration declarations."""

from __future__ import annotations

import copy
import dataclasses
import pickle
import sys
import unittest
from typing import Annotated, Generic, TypeVar

from temporal import Action, Constant, Domain, Model, ModelValue, State, Symmetry

T = TypeVar("T")


class Proc(ModelValue):
    pass


class Msg(ModelValue):
    pass


class DummySpec:
    procs: Constant[frozenset[Proc]]
    x: State[int] = 0

    def step(self) -> Annotated[None, Action()]:
        self.x += 1


class GenericSpec(Generic[T]):
    item: State[T]


class TestModelValue(unittest.TestCase):
    def test_equality_disjoint_sorts_and_hashing(self) -> None:
        a1, a2, b = ModelValue("a"), ModelValue("a"), ModelValue("b")
        p, m = Proc("a"), Msg("a")

        self.assertEqual(a1, a2)
        self.assertEqual(hash(a1), hash(a2))
        self.assertNotEqual(a1, b)
        self.assertNotEqual(a1, "a")
        self.assertNotEqual(p, a1)
        self.assertNotEqual(p, m)
        self.assertEqual(p, Proc("a"))
        self.assertEqual(hash(p), hash(Proc("a")))

    def test_unordered_immutable_and_picklable(self) -> None:
        p1, p2 = Proc("p1"), Proc("p2")
        with self.assertRaises(TypeError):
            _ = p1 < p2  # type: ignore[operator]
        with self.assertRaises(dataclasses.FrozenInstanceError):
            p1.name = "p3"  # type: ignore[misc]

        self.assertEqual(str(p1), "p1")
        self.assertEqual(repr(p1), "Proc('p1')")
        self.assertEqual(pickle.loads(pickle.dumps(p1)), p1)
        self.assertIs(type(pickle.loads(pickle.dumps(p1))), Proc)
        self.assertEqual(copy.deepcopy(p1), p1)


class TestSymmetry(unittest.TestCase):
    def test_frozenset_semantics_and_pickle(self) -> None:
        p1, p2 = Proc("p1"), Proc("p2")
        sym = Symmetry({p1, p2})
        self.assertIsInstance(sym, Symmetry)
        self.assertIsInstance(sym, frozenset)
        self.assertEqual(sym, frozenset({p1, p2}))
        self.assertEqual(hash(sym), hash(frozenset({p1, p2})))
        self.assertEqual(repr(Symmetry()), "Symmetry()")
        self.assertTrue(repr(sym).startswith("Symmetry({"))
        self.assertIs(type(sym | frozenset({Proc("p3")})), frozenset)

        restored = pickle.loads(pickle.dumps(sym))
        self.assertIsInstance(restored, Symmetry)
        self.assertEqual(restored, sym)


class TestDomain(unittest.TestCase):
    def test_range_values_and_boolean(self) -> None:
        r = Domain.range(0, 3)
        self.assertEqual(list(r), [0, 1, 2, 3])
        self.assertEqual(len(r), 4)
        self.assertIn(3, r)
        self.assertNotIn(4, r)
        self.assertEqual(repr(r), "Domain.range(0, 3)")
        self.assertEqual(pickle.loads(pickle.dumps(r)), r)

        v = Domain.values("alice", "bob")
        self.assertEqual(list(v), ["alice", "bob"])
        self.assertEqual(repr(v), "Domain.values('alice', 'bob')")

        # (0, 1) must not be confused with (False, True).
        zero_one = Domain.values(0, 1)
        self.assertEqual(repr(zero_one), "Domain.values(0, 1)")

        b = Domain.boolean()
        self.assertEqual(list(b), [False, True])
        self.assertEqual(repr(b), "Domain.boolean()")
        self.assertEqual(hash(b), hash(Domain.boolean()))


class TestModel(unittest.TestCase):
    def test_defaults_repr_replace_and_pickle(self) -> None:
        m = Model(DummySpec)
        self.assertIs(m.spec, DummySpec)
        self.assertEqual(m.constants, {})
        self.assertEqual(m.domains, {})
        self.assertIsNone(m.init)
        self.assertIsNone(m.actions)
        self.assertIsNone(m.invariants)
        self.assertIsNone(m.properties)
        self.assertTrue(m.check_deadlock)
        self.assertEqual(repr(m), f"Model({DummySpec!r})")

        procs = Symmetry({Proc("p1"), Proc("p2")})
        m2 = dataclasses.replace(
            m,
            constants={"procs": procs},
            domains={Proc: procs, int: Domain.range(0, 2)},
            check_deadlock=False,
        )
        self.assertFalse(m2.check_deadlock)
        self.assertEqual(m2.constants["procs"], procs)
        self.assertEqual(pickle.loads(pickle.dumps(m2)), m2)
        self.assertEqual(copy.deepcopy(m2), m2)

        with self.assertRaises(dataclasses.FrozenInstanceError):
            m.check_deadlock = False  # type: ignore[misc]

    def test_module_and_generic_alias_specs(self) -> None:
        m_generic = Model(GenericSpec[int], domains={int: Domain.range(0, 2)})
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


if __name__ == "__main__":
    unittest.main()
