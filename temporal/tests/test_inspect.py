"""Tests for passive Temporal reflection helpers (get_metadata, get_contract, get_spec)."""

from __future__ import annotations

import types
import unittest
from typing import Annotated, Any, Generic, Protocol, TypeVar

from temporal import (
    Action,
    ActionInvariant,
    Assume,
    Const,
    Ensures,
    Fairness,
    Ghost,
    Init,
    Invariant,
    Modifies,
    Property,
    Pure,
    Refines,
    Requires,
    Role,
    State,
    StrongFairness,
    Unchanged,
    WeakFairness,
    Where,
    always,
    get_contract,
    get_metadata,
    get_role,
    get_spec,
    is_temporal_metadata,
    leads_to,
    old,
    prime,
    strip_temporal,
    weak_fairness,
)

T = TypeVar("T")
Positive = Annotated[int, Where(lambda x: x > 0, "positive")]
NonNegative = Annotated[int, Where(lambda x: x >= 0)]


class AbstractCounter(Protocol):
    limit: Const[Positive]
    count: State[NonNegative]

    def assume_limit(self) -> Assume:
        return self.limit > 0

    def init(self) -> Init:
        return self.count == 0

    def bounded(self) -> Invariant:
        return self.count <= self.limit

    def monotonic(self) -> ActionInvariant:
        return prime(self.count) >= self.count

    def step(self, delta: Positive) -> Annotated[
        Action[NonNegative],
        Requires(lambda self, delta: self.count + delta <= self.limit),
        Ensures(lambda self, delta, result: self.count == old(self.count) + delta and result == self.count),
        Modifies("count"),
        Unchanged("limit"),
        WeakFairness(),
    ]: ...

    def reaches_limit(self) -> Property:
        return leads_to(self.count < self.limit, self.count == self.limit)

    def fair(self) -> Fairness:
        return weak_fairness(self.step)


class ConcreteCounter(AbstractCounter):
    history: Ghost[tuple[int, ...]] = (0,)

    @property
    def is_full(self) -> Pure[bool]:
        return self.count == self.limit

    @staticmethod
    def helper(x: Positive) -> Pure[Positive]:
        return x

    def as_abstract(self) -> Refines[AbstractCounter]:
        return Refines(limit=self.limit, count=self.count)


class GenericBox(Generic[T]):
    item: State[T]

    def swap(self, new_item: T) -> Annotated[Action[T], StrongFairness("item")]:
        raise NotImplementedError


def standalone_add(
    a: Positive,
    b: Positive,
) -> Annotated[
    Pure[Positive],
    Requires(lambda a, b: a + b < 100),
    Ensures(lambda a, b, result: result == a + b),
]:
    return a + b


def plain_function(x: int) -> int:
    return x + 1


def unannotated_function(x):  # type: ignore[no-untyped-def]
    return x


class TestMetadataHelpers(unittest.TestCase):
    def test_is_temporal_metadata(self) -> None:
        self.assertTrue(is_temporal_metadata(Role.STATE))
        self.assertTrue(is_temporal_metadata(Where(lambda x: True)))
        self.assertTrue(is_temporal_metadata(Requires(lambda: True)))
        self.assertTrue(is_temporal_metadata(Ensures(lambda: True)))
        self.assertTrue(is_temporal_metadata(Modifies("x")))
        self.assertTrue(is_temporal_metadata(Unchanged("x")))
        self.assertTrue(is_temporal_metadata(WeakFairness()))
        self.assertTrue(is_temporal_metadata(StrongFairness()))
        self.assertFalse(is_temporal_metadata("plain"))
        self.assertFalse(is_temporal_metadata(42))

    def test_plain_types(self) -> None:
        self.assertEqual(get_metadata(int), ())
        self.assertIsNone(get_role(int))
        self.assertIs(strip_temporal(int), int)
        self.assertEqual(repr(Role.STATE), "Role.STATE")
        self.assertEqual(repr(Role.ACTION_INVARIANT), "Role.ACTION_INVARIANT")


class TestGetContract(unittest.TestCase):
    def test_standalone_contract(self) -> None:
        c = get_contract(standalone_add)
        self.assertTrue(c.is_temporal)
        self.assertIs(c.role, Role.PURE)
        self.assertIs(c.return_type, int)
        self.assertEqual(len(c.requires), 1)
        self.assertEqual(len(c.ensures), 1)
        self.assertEqual(len(c.return_refinements), 1)
        self.assertEqual(c.return_refinements[0].description, "positive")
        self.assertEqual(set(c.param_refinements.keys()), {"a", "b"})
        self.assertIsNone(c.refines)

    def test_plain_and_unannotated_functions(self) -> None:
        c_plain = get_contract(plain_function)
        self.assertFalse(c_plain.is_temporal)
        self.assertIsNone(c_plain.role)
        self.assertIs(c_plain.return_type, int)

        c_unann = get_contract(unannotated_function)
        self.assertFalse(c_unann.is_temporal)
        self.assertIsNone(c_unann.role)
        self.assertIs(c_unann.return_type, Any)

    def test_descriptors(self) -> None:
        prop_c = get_contract(ConcreteCounter.is_full)
        self.assertIs(prop_c.role, Role.PURE)
        self.assertIs(prop_c.return_type, bool)

        static_c = get_contract(ConcreteCounter.__dict__["helper"])
        self.assertIs(static_c.role, Role.PURE)
        self.assertIn("x", static_c.param_refinements)

    def test_refines_bare_and_annotated(self) -> None:
        def bare() -> Refines[Any]:
            return Refines()

        def bare_unparam() -> Refines:  # type: ignore[type-arg]
            return Refines()

        def annotated_ref() -> Annotated[Refines[AbstractCounter], "tag"]:
            return Refines()

        self.assertIs(get_contract(bare).refines, Any)
        self.assertIs(get_contract(bare_unparam).refines, Any)
        self.assertIs(get_contract(annotated_ref).refines, AbstractCounter)

    def test_callable_object(self) -> None:
        class Adder:
            def __call__(
                self, x: Positive
            ) -> Annotated[int, Ensures(lambda self, x, result: result > x)]:
                return x + 1

        c = get_contract(Adder())
        self.assertTrue(c.is_temporal)
        self.assertIsNone(c.role)
        self.assertIn("x", c.param_refinements)
        self.assertEqual(len(c.ensures), 1)

    def test_errors(self) -> None:
        with self.assertRaises(TypeError):
            get_contract(123)
        with self.assertRaises(TypeError):
            get_contract(ConcreteCounter)

        def bad_return() -> State[int]:
            return 0

        with self.assertRaises(ValueError):
            get_contract(bad_return)


class TestGetSpec(unittest.TestCase):
    def test_protocol_and_inheritance(self) -> None:
        spec = get_spec(ConcreteCounter)
        self.assertIs(spec.target, ConcreteCounter)
        self.assertEqual(set(spec.constants.keys()), {"limit"})
        self.assertEqual(spec.constants["limit"].type, int)
        self.assertEqual(len(spec.constants["limit"].refinements), 1)
        self.assertEqual(set(spec.state.keys()), {"count"})
        self.assertEqual(set(spec.ghost.keys()), {"history"})
        self.assertEqual(set(spec.assumptions.keys()), {"assume_limit"})
        self.assertEqual(set(spec.inits.keys()), {"init"})
        self.assertEqual(set(spec.actions.keys()), {"step"})
        self.assertEqual(set(spec.pure.keys()), {"is_full", "helper"})
        self.assertEqual(set(spec.invariants.keys()), {"bounded"})
        self.assertEqual(set(spec.action_invariants.keys()), {"monotonic"})
        self.assertEqual(set(spec.properties.keys()), {"reaches_limit"})
        self.assertEqual(set(spec.fairness.keys()), {"fair"})
        self.assertEqual(dict(spec.refinements), {"as_abstract": AbstractCounter})

        step = spec.actions["step"]
        self.assertEqual(step.modifies, (Modifies("count"),))
        self.assertEqual(step.unchanged, (Unchanged("limit"),))
        self.assertEqual(step.fairness, (WeakFairness(),))

    def test_generic_alias_spec(self) -> None:
        spec = get_spec(GenericBox[int])
        self.assertEqual(spec.target, GenericBox[int])
        self.assertEqual(set(spec.state.keys()), {"item"})
        self.assertEqual(set(spec.actions.keys()), {"swap"})
        self.assertEqual(spec.actions["swap"].fairness, (StrongFairness("item"),))

    def test_module_spec_ignores_imported_functions(self) -> None:
        mod = types.ModuleType("sample_mod")
        mod.__annotations__ = {
            "N": Const[int],
            "x": State[int],
        }

        def init() -> Init:
            return True

        def step() -> Action[bool]:
            return always(True)

        init.__module__ = "sample_mod"
        step.__module__ = "sample_mod"
        mod.init = init  # type: ignore[attr-defined]
        mod.step = step  # type: ignore[attr-defined]
        # Foreign function imported into the module must NOT be collected.
        mod.standalone_add = standalone_add  # type: ignore[attr-defined]

        spec = get_spec(mod)
        self.assertEqual(set(spec.constants.keys()), {"N"})
        self.assertEqual(set(spec.state.keys()), {"x"})
        self.assertEqual(set(spec.inits.keys()), {"init"})
        self.assertEqual(set(spec.actions.keys()), {"step"})
        self.assertEqual(set(spec.pure.keys()), set())

    def test_passivity(self) -> None:
        class Explosive:
            x: State[int] = 0

            def inv(self) -> Invariant:
                raise AssertionError("Must not be called")

            def prop(self) -> Property:
                return always(self.x >= 0)

        spec = get_spec(Explosive)
        self.assertEqual(set(spec.invariants.keys()), {"inv"})
        self.assertEqual(set(spec.properties.keys()), {"prop"})

    def test_dunder_and_roleless_contracts(self) -> None:
        class Service:
            builtin_attr = len
            type_attr = dict
            x: State[int] = 0

            def __init__(self, initial: Positive) -> Annotated[
                None, Ensures(lambda self, initial: self.x == initial)
            ]:
                self.x = initial

            def parse(
                self, raw: Positive
            ) -> Annotated[int, Ensures(lambda raw, result: result == raw)]:
                return raw

        spec = get_spec(Service)
        self.assertEqual(set(spec.state), {"x"})
        self.assertEqual(set(spec.contracts), {"__init__", "parse"})

    def test_errors(self) -> None:
        with self.assertRaises(TypeError):
            get_spec(42)
        with self.assertRaises(TypeError):
            get_spec(plain_function)

        class BadAttr:
            x: Action[int]

        with self.assertRaises(ValueError):
            get_spec(BadAttr)


if __name__ == "__main__":
    unittest.main()
