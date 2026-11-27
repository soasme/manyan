"""Temporal: behavioural specification declarations for Python, grounded in TLA+.

Temporal is a pure, passive declaration library with zero third-party
dependencies. Specifications are expressed directly in Python using PEP 593
``Annotated`` type annotations and Python expressions; verification is
performed externally by tools such as Manyan.

Declaration annotations follow TLA+'s four expression levels:

- Level 0 (Constant): ``Const[T]``, ``Assume``
- Level 1 (State):    ``State[T]``, ``Ghost[T]``, ``Init``, ``Pure[T]``, ``Invariant``
- Level 2 (Action):   ``Action[T]``, ``ActionInvariant``
- Level 3 (Temporal): ``Property``, ``Fairness``
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from enum import Enum
from types import ModuleType
from typing import Annotated, Any, Generic, Optional, TypeVar, Union

__version__ = "0.1.0"

_T = TypeVar("_T")
_T_co = TypeVar("_T_co", covariant=True)


# ---------------------------------------------------------------------------
# Declaration roles and PEP 593 Annotated type aliases
# ---------------------------------------------------------------------------


class Role(Enum):
    """TLA+ declaration role carried inside PEP 593 ``Annotated`` metadata."""

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


Const = Annotated[_T, Role.CONST]
State = Annotated[_T, Role.STATE]
Ghost = Annotated[_T, Role.GHOST]
Assume = Annotated[bool, Role.ASSUME]
Init = Annotated[bool, Role.INIT]
Pure = Annotated[_T, Role.PURE]
Action = Annotated[_T, Role.ACTION]
Invariant = Annotated[bool, Role.INVARIANT]
ActionInvariant = Annotated[bool, Role.ACTION_INVARIANT]
Property = Annotated[bool, Role.PROPERTY]
Fairness = Annotated[bool, Role.FAIRNESS]


# ---------------------------------------------------------------------------
# Contract, framing, fairness, and refinement clauses
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _PredicateClause:
    predicate: Callable[..., bool]
    description: Optional[str] = None

    def __repr__(self) -> str:
        name = type(self).__name__
        if self.description is None:
            return f"{name}({self.predicate!r})"
        return f"{name}({self.predicate!r}, {self.description!r})"


@dataclass(frozen=True, repr=False)
class Where(_PredicateClause):
    """Refinement predicate on a type: ``{x \\in T : predicate(x)}``."""

    predicate: Callable[[Any], bool]
    description: Optional[str] = None


@dataclass(frozen=True, repr=False)
class Requires(_PredicateClause):
    """Precondition or enabling guard on a function or action."""


@dataclass(frozen=True, repr=False)
class Ensures(_PredicateClause):
    """Postcondition on a function or action (``old(e)`` is pre-state, ``e`` is post-state)."""


@dataclass(frozen=True)
class _VariableClause:
    variables: tuple[str, ...]

    def __init__(self, *variables: str) -> None:
        object.__setattr__(self, "variables", variables)

    def __repr__(self) -> str:
        args = ", ".join(repr(v) for v in self.variables)
        return f"{type(self).__name__}({args})"


@dataclass(frozen=True, init=False, repr=False)
class Modifies(_VariableClause):
    """Frame clause: only the named state variables may change."""


@dataclass(frozen=True, init=False, repr=False)
class Unchanged(_VariableClause):
    """Frame clause: the named state variables remain ``UNCHANGED``."""


@dataclass(frozen=True, init=False, repr=False)
class WeakFairness(_VariableClause):
    """Weak fairness metadata on an action: ``WF_v(action)``."""


@dataclass(frozen=True, init=False, repr=False)
class StrongFairness(_VariableClause):
    """Strong fairness metadata on an action: ``SF_v(action)``."""


@dataclass(frozen=True)
class Refines(Generic[_T_co]):
    """Refinement mapping to an abstract specification (TLA+ ``INSTANCE ... WITH``)."""

    mapping: Mapping[str, Any]

    def __init__(self, **mapping: Any) -> None:
        object.__setattr__(self, "mapping", mapping)

    def __repr__(self) -> str:
        items = ", ".join(f"{k}={v!r}" for k, v in self.mapping.items())
        return f"Refines({items})"


# ---------------------------------------------------------------------------
# Declarative TLA+ expression primitives
# ---------------------------------------------------------------------------


def _declarative(name: str) -> NotImplementedError:
    return NotImplementedError(f"{name}() is a declarative Temporal primitive")


def implies(antecedent: bool, consequent: bool) -> bool:
    """Logical implication: ``antecedent => consequent``."""
    raise _declarative("implies")


def iff(left: bool, right: bool) -> bool:
    """Logical equivalence: ``left <=> right``."""
    raise _declarative("iff")


def choose(
    domain: Iterable[_T],
    predicate: Optional[Callable[[_T], bool]] = None,
) -> _T:
    """Hilbert's choice operator: ``CHOOSE x \\in domain : predicate(x)``."""
    raise _declarative("choose")


def old(value: _T) -> _T:
    """Pre-state value of ``value`` inside an ``Ensures`` postcondition."""
    raise _declarative("old")


def prime(value: _T) -> _T:
    """Next-state value ``value'`` inside an action or ``ActionInvariant``."""
    raise _declarative("prime")


def unchanged(*values: Any) -> bool:
    """Stuttering predicate: ``UNCHANGED <<v1, v2, ...>>``."""
    raise _declarative("unchanged")


def enabled(action: Any) -> bool:
    """Enabling predicate: ``ENABLED action``."""
    raise _declarative("enabled")


def always(formula: bool) -> bool:
    """Temporal safety operator: ``[]formula``."""
    raise _declarative("always")


def eventually(formula: bool) -> bool:
    """Temporal liveness operator: ``<>formula``."""
    raise _declarative("eventually")


def leads_to(cause: bool, effect: bool) -> bool:
    """Temporal leads-to operator: ``cause ~> effect``."""
    raise _declarative("leads_to")


def weak_fairness(action: Any, *, on: Any = None) -> bool:
    """Weak fairness operator: ``WF_on(action)``."""
    raise _declarative("weak_fairness")


def strong_fairness(action: Any, *, on: Any = None) -> bool:
    """Strong fairness operator: ``SF_on(action)``."""
    raise _declarative("strong_fairness")


# ---------------------------------------------------------------------------
# Model configuration and symbolic values
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ModelValue:
    """Uninterpreted TLA+ model value; subclass to define disjoint sorts."""

    name: str

    def __eq__(self, other: object) -> bool:
        return type(self) is type(other) and self.name == getattr(other, "name", None)

    def __hash__(self) -> int:
        return hash((type(self), self.name))

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return f"{type(self).__name__}({self.name!r})"


class Symmetry(frozenset[_T_co]):
    """Immutable finite set marked as symmetric (TLA+ ``SYMMETRY``)."""

    def __repr__(self) -> str:
        if not self:
            return f"{type(self).__name__}()"
        return f"{type(self).__name__}({set(self)!r})"

    def __reduce__(self) -> tuple[type[Symmetry[_T_co]], tuple[tuple[_T_co, ...]]]:
        return (type(self), (tuple(self),))


def _empty_dict() -> dict[Any, Any]:
    return {}


@dataclass(frozen=True)
class Model:
    """Declarative model configuration (Python equivalent of a TLA+ ``.cfg``)."""

    spec: Union[type[Any], ModuleType]
    constants: Mapping[str, Any] = field(default_factory=_empty_dict)
    domains: Mapping[Any, Iterable[Any]] = field(default_factory=_empty_dict)
    init: Optional[Callable[..., Any]] = None
    actions: Optional[Sequence[Callable[..., Any]]] = None
    invariants: Optional[Sequence[Callable[..., Any]]] = None
    properties: Optional[Sequence[Callable[..., Any]]] = None
    state_constraint: Optional[Callable[..., bool]] = None
    action_constraint: Optional[Callable[..., bool]] = None
    symmetry: Sequence[Symmetry[Any]] = ()
    view: Optional[Callable[..., Any]] = None
    alias: Optional[Callable[..., Any]] = None
    postcondition: Optional[Callable[..., bool]] = None
    check_deadlock: bool = True

    def __repr__(self) -> str:
        parts = [repr(self.spec)]
        if self.constants:
            parts.append(f"constants={self.constants!r}")
        if self.domains:
            parts.append(f"domains={self.domains!r}")
        for attr in (
            "init",
            "actions",
            "invariants",
            "properties",
            "state_constraint",
            "action_constraint",
            "view",
            "alias",
            "postcondition",
        ):
            val = getattr(self, attr)
            if val is not None:
                parts.append(f"{attr}={val!r}")
        if self.symmetry:
            parts.append(f"symmetry={self.symmetry!r}")
        if not self.check_deadlock:
            parts.append("check_deadlock=False")
        return f"Model({', '.join(parts)})"


__all__ = [
    "Action",
    "ActionInvariant",
    "Assume",
    "Const",
    "Ensures",
    "Fairness",
    "Ghost",
    "Init",
    "Invariant",
    "Model",
    "ModelValue",
    "Modifies",
    "Property",
    "Pure",
    "Refines",
    "Requires",
    "Role",
    "State",
    "StrongFairness",
    "Symmetry",
    "Unchanged",
    "WeakFairness",
    "Where",
    "__version__",
    "always",
    "choose",
    "enabled",
    "eventually",
    "iff",
    "implies",
    "leads_to",
    "old",
    "prime",
    "strong_fairness",
    "unchanged",
    "weak_fairness",
]
