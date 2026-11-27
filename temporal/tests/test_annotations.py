"""Tests for PEP 593 declaration annotations, typing integration, and zero dependencies."""

from __future__ import annotations

import ast
import dataclasses
import sys
import unittest
from pathlib import Path
from typing import (
    Annotated,
    ClassVar,
    Generic,
    Protocol,
    TypeVar,
    get_args,
    get_origin,
    get_type_hints,
)

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
)

T = TypeVar("T")
Positive = Annotated[int, Where(lambda x: x > 0)]


class TestDeclarationAnnotations(unittest.TestCase):
    def test_all_roles_covered(self) -> None:
        role_map = {
            Role.CONST: (Const[int], int),
            Role.STATE: (State[int], int),
            Role.GHOST: (Ghost[tuple[int, ...]], tuple[int, ...]),
            Role.ASSUME: (Assume, bool),
            Role.INIT: (Init, bool),
            Role.PURE: (Pure[float], float),
            Role.ACTION: (Action[None], type(None)),
            Role.INVARIANT: (Invariant, bool),
            Role.ACTION_INVARIANT: (ActionInvariant, bool),
            Role.PROPERTY: (Property, bool),
            Role.FAIRNESS: (Fairness, bool),
        }
        self.assertEqual(set(role_map), set(Role))
        for role, (ann, underlying) in role_map.items():
            self.assertIs(get_origin(ann), Annotated)
            args = get_args(ann)
            self.assertEqual(args[0], underlying)
            self.assertIs(args[1], role)
            self.assertEqual(repr(role), f"Role.{role.name}")

    def test_annotated_flattening(self) -> None:
        req = Requires(lambda self, x: x > 0)
        ens = Ensures(lambda self, x, result: result == x)
        combined = Annotated[Action[int], req, ens]
        self.assertIs(get_origin(combined), Annotated)
        self.assertEqual(get_args(combined), (int, Role.ACTION, req, ens))

        inv_pred = lambda self: True
        inv_ann = Annotated[Invariant, inv_pred]
        self.assertEqual(get_args(inv_ann), (bool, Role.INVARIANT, inv_pred))

    def test_composed_refined_type_alias(self) -> None:
        state_pos = State[Positive]
        args = get_args(state_pos)
        self.assertIs(args[0], int)
        self.assertIsInstance(args[1], Where)
        self.assertIs(args[2], Role.STATE)

    def test_dataclass_and_signature_level_annotations(self) -> None:
        @dataclasses.dataclass
        class Jugs:
            capacity: Const[int]
            level: State[int] = 0
            moves: Ghost[int] = 0

            bounded: ClassVar[Annotated[Invariant, lambda self: 0 <= self.level <= self.capacity]]

        j = Jugs(capacity=5)
        self.assertEqual(dataclasses.asdict(j), {"capacity": 5, "level": 0, "moves": 0})
        self.assertEqual([f.name for f in dataclasses.fields(Jugs)], ["capacity", "level", "moves"])
        self.assertFalse(hasattr(j, "bounded"))

        hints = get_type_hints(Jugs, localns=locals(), include_extras=True)
        self.assertIs(get_args(hints["capacity"])[1], Role.CONST)
        self.assertIs(get_args(hints["level"])[1], Role.STATE)
        self.assertIs(get_args(hints["moves"])[1], Role.GHOST)
        self.assertIs(get_origin(hints["bounded"]), ClassVar)

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
        self.assertIs(get_args(hints["value"])[1], Role.STATE)

    def test_single_module_and_zero_third_party_dependencies(self) -> None:
        pkg_dir = Path(temporal.__file__).resolve().parent
        py_files = sorted(pkg_dir.glob("*.py"))
        self.assertEqual([p.name for p in py_files], ["__init__.py"])

        stdlib = getattr(sys, "stdlib_module_names", None)
        tree = ast.parse(py_files[0].read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    top = alias.name.split(".")[0]
                    if stdlib is not None:
                        self.assertIn(top, stdlib)
            elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                top = node.module.split(".")[0]
                if stdlib is not None:
                    self.assertIn(top, stdlib)

    def test_all_exports_present_and_sorted(self) -> None:
        self.assertEqual(temporal.__all__, sorted(temporal.__all__))
        for name in temporal.__all__:
            self.assertTrue(hasattr(temporal, name), f"Missing export {name!r}")


if __name__ == "__main__":
    unittest.main()
