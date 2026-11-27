"""Core declaration type annotations grounded in TLA+'s four expression levels.

Level 0 (Constant):  Const[T], Assume
Level 1 (State):     State[T], Ghost[T], Init, Pure[T], Invariant
Level 2 (Action):    Action[T], ActionInvariant
Level 3 (Temporal):  Property, Fairness

All annotations are PEP 593 Annotated aliases, so static type checkers
(mypy, Pyright) treat them as their underlying Python types while preserving
exact specification metadata for verification tools such as Manyan.
"""

from __future__ import annotations

from enum import Enum
from typing import Annotated, TypeVar

_T = TypeVar("_T")


class Role(Enum):
    """TLA+ declaration role attached to a Python type annotation."""

    CONST = "const"
    STATE = "state"
    GHOST = "ghost"
    ASSUME = "assume"
    INIT = "init"
    PURE = "pure"
    ACTION = "action"
    INVARIANT = "invariant"
    ACTION_INVARIANT = "action_invariant"
    PROPERTY = "property"
    FAIRNESS = "fairness"

    def __repr__(self) -> str:
        return f"Role.{self.name}"


# Variable and constant declarations (class or module attributes)
Const = Annotated[_T, Role.CONST]
State = Annotated[_T, Role.STATE]
Ghost = Annotated[_T, Role.GHOST]

# Callable declarations (methods or module-level functions)
Assume = Annotated[bool, Role.ASSUME]
Init = Annotated[bool, Role.INIT]
Pure = Annotated[_T, Role.PURE]
Action = Annotated[_T, Role.ACTION]
Invariant = Annotated[bool, Role.INVARIANT]
ActionInvariant = Annotated[bool, Role.ACTION_INVARIANT]
Property = Annotated[bool, Role.PROPERTY]
Fairness = Annotated[bool, Role.FAIRNESS]
