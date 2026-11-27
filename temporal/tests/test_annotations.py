"""Tests for Temporal declaration annotations, typing integration, and zero dependencies."""

from __future__ import annotations

import ast
import dataclasses
import sys
import unittest
from pathlib import Path
from typing import Annotated, Generic, Protocol, TypeVar, get_args, get_origin, get_type_hints

import temporal
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
    Property,
    Pure,
    Requires,
    Role,
    State,
    Where,
    get_metadata,
    get_role,
    strip_temporal,
)

T = TypeVar("T")
Positive = Annotated[int, Where(lambda x: x > 0)]


class TestDeclarationAliases(unittest.TestCase):
    def test_all_roles_covered(self) -> None:
        role_map = {
            Role.CONST: Const[int],
            Role.STATE: State[int],
            Role.GHOST: Ghost[int],
            Role.ASSUME: Assume,
            Role.INIT: Init,
            Role.PURE: Pure[int],
            Role.ACTION: Action[None],
            Role.INVARIANT: Invariant,
            Role.ACTION_INVARIANT: ActionInvariant,
            Role.PROPERTY: Property,
            Role.FAIRNESS: Fairness,
        }
        self.assertEqual(set(role_map.keys()), set(Role))
        for expected_role, ann in role_map.items():
            self.assertIs(get_origin(ann), Annotated)
            self.assertIs(get_role(ann), expected_role)

    def test_underlying_types(self) -> None:
        self.assertIs(strip_temporal(Const[str]), str)
        self.assertIs(strip_temporal(State[int]), int)
        self.assertEqual(strip_temporal(Ghost[tuple[int, ...]]), tuple[int, ...])
        self.assertIs(strip_temporal(Pure[float]), float)
        self.assertIs(strip_temporal(Action[int]), int)
        self.assertIs(strip_temporal(Action[None]), type(None))
        for bool_ann in (Assume, Init, Invariant, ActionInvariant, Property, Fairness):
            self.assertIs(strip_temporal(bool_ann), bool)

    def test_annotated_flattening(self) -> None:
        req = Requires(lambda self, x: x > 0)
        ens = Ensures(lambda self, x, result: result == x)
        combined = Annotated[Action[int], req, ens]
        self.assertIs(get_origin(combined), Annotated)
        self.assertEqual(get_args(combined), (int, Role.ACTION, req, ens))
        self.assertIs(get_role(combined), Role.ACTION)
        self.assertEqual(get_metadata(combined), (Role.ACTION, req, ens))

    def test_composed_refined_type_alias(self) -> None:
        state_pos = State[Positive]
        self.assertIs(get_role(state_pos), Role.STATE)
        self.assertIs(strip_temporal(state_pos), int)
        meta = get_metadata(state_pos)
        self.assertEqual(len(meta), 2)
        self.assertIsInstance(meta[0], Where)
        self.assertIs(meta[1], Role.STATE)

    def test_foreign_metadata_preserved(self) -> None:
        class ForeignTag:
            pass

        tag = ForeignTag()
        ann = Annotated[State[int], tag, "doc"]
        self.assertIs(get_role(ann), Role.STATE)
        self.assertEqual(get_metadata(ann), (Role.STATE,))
        stripped = strip_temporal(ann)
        self.assertIs(get_origin(stripped), Annotated)
        self.assertEqual(get_args(stripped), (int, tag, "doc"))

    def test_conflicting_roles_rejected(self) -> None:
        with self.assertRaises(ValueError):
            get_role(State[Const[int]])
        with self.assertRaises(ValueError):
            get_role(Annotated[Init, Role.INVARIANT])

    def test_duplicate_same_role_allowed(self) -> None:
        self.assertIs(get_role(Annotated[State[int], Role.STATE]), Role.STATE)

    def test_dataclass_interoperability(self) -> None:
        @dataclasses.dataclass
        class Jugs:
            capacity: Const[int]
            level: State[int] = 0
            moves: Ghost[int] = 0

            def invariant(self) -> Invariant:
                return 0 <= self.level <= self.capacity

        j = Jugs(capacity=5)
        self.assertEqual(j.capacity, 5)
        self.assertEqual(j.level, 0)
        self.assertEqual(j.moves, 0)
        self.assertTrue(j.invariant())
        self.assertEqual(dataclasses.asdict(j), {"capacity": 5, "level": 0, "moves": 0})
        field_names = [f.name for f in dataclasses.fields(Jugs)]
        self.assertEqual(field_names, ["capacity", "level", "moves"])

    def test_protocol_and_generic_interoperability(self) -> None:
        class Box(Protocol[T]):
            value: State[T]

            def get(self) -> Pure[T]: ...

        class SimpleBox(Generic[T]):
            value: State[T]

            def __init__(self, value: T) -> None:
                self.value = value

            def get(self) -> Pure[T]:
                return self.value

        b: SimpleBox[int] = SimpleBox(42)
        self.assertEqual(b.get(), 42)
        hints = get_type_hints(Box, localns={"T": T}, include_extras=True)
        self.assertIs(get_role(hints["value"]), Role.STATE)

    def test_zero_third_party_dependencies(self) -> None:
        pkg_dir = Path(temporal.__file__).resolve().parent
        stdlib = getattr(sys, "stdlib_module_names", None)
        for py_file in sorted(pkg_dir.glob("*.py")):
            tree = ast.parse(py_file.read_text(encoding="utf-8"))
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        top = alias.name.split(".")[0]
                        if stdlib is not None:
                            self.assertIn(top, stdlib, f"Non-stdlib import {top!r} in {py_file.name}")
                elif isinstance(node, ast.ImportFrom):
                    if node.level > 0:
                        continue
                    assert node.module is not None
                    top = node.module.split(".")[0]
                    if stdlib is not None:
                        self.assertIn(top, stdlib, f"Non-stdlib import {top!r} in {py_file.name}")

    def test_all_exports_present_and_sorted(self) -> None:
        self.assertEqual(temporal.__all__, sorted(temporal.__all__))
        for name in temporal.__all__:
            self.assertTrue(hasattr(temporal, name), f"Missing export {name!r}")


if __name__ == "__main__":
    unittest.main()
