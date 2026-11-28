"""Temporal: behavioural specification declarations for Python, grounded in TLA+.

Temporal is a pure, passive declaration library with zero third-party
dependencies. Specifications are declared at the signature level using PEP 593
``Annotated`` type annotations and Python expressions; verification is
performed externally by tools such as Manyan.

Declarations follow TLA+'s four semantic levels:

- Level 0 (Constant): ``Constant[T]``, ``Assume``
- Level 1 (State):    ``State[T]``, ``Ghost[T]``, ``Pure[T]``, ``Init``, ``Invariant``
- Level 2 (Action):   ``Action``, ``ActionInvariant``, ``Requires``, ``Ensures``,
                      ``Preserves``, ``Modifies``, ``Unchanged``
- Level 3 (Temporal): ``Property``, ``Fairness``, ``WeakFairness``, ``StrongFairness``
"""

from __future__ import annotations

from collections.abc import Callable, Collection, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from enum import Enum
from typing import Annotated, Any, Generic, Optional, TypeVar, Union

__version__ = "0.1.0"

_T = TypeVar("_T")
_T_co = TypeVar("_T_co", covariant=True)


# ---------------------------------------------------------------------------
# Value-level type qualifiers (PEP 593 Annotated aliases)
# ---------------------------------------------------------------------------


class Role(Enum):
    """TLA+ variable or operator qualifier carried in ``Annotated`` metadata."""

    CONSTANT = "constant"
    STATE = "state"
    GHOST = "ghost"
    PURE = "pure"

    def __repr__(self) -> str:
        return f"Role.{self.name}"


Constant = Annotated[_T, Role.CONSTANT]
State = Annotated[_T, Role.STATE]
Ghost = Annotated[_T, Role.GHOST]
Pure = Annotated[_T, Role.PURE]


# ---------------------------------------------------------------------------
# Specification, contract, framing, fairness, and refinement clauses
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _OptionalPredicateClause:
    predicate: Optional[Callable[..., bool]] = None
    description: Optional[str] = None

    def __repr__(self) -> str:
        name = type(self).__name__
        if self.predicate is None and self.description is None:
            return f"{name}()"
        if self.description is None:
            return f"{name}({self.predicate!r})"
        if self.predicate is None:
            return f"{name}(description={self.description!r})"
        return f"{name}({self.predicate!r}, {self.description!r})"


@dataclass(frozen=True, repr=False)
class Assume(_OptionalPredicateClause):
    """Constant-level assumption: ``ASSUME P``."""


@dataclass(frozen=True, repr=False)
class Init(_OptionalPredicateClause):
    """Initial-state predicate: ``Init``."""


@dataclass(frozen=True, repr=False)
class Action(_OptionalPredicateClause):
    """Atomic state transition action (TLA+ ``Next`` disjunct).

    - ``Action(predicate)`` declares an explicit two-state relation over
      pre-state (``s.x``) and post-state (``prime(s.x)``).
    - ``Action()`` marks a method or function whose body defines the transition.
    """


@dataclass(frozen=True, repr=False)
class Invariant(_OptionalPredicateClause):
    """State invariant verified across all reachable states: ``[]I``."""


@dataclass(frozen=True, repr=False)
class ActionInvariant(_OptionalPredicateClause):
    """Two-state action invariant verified on every step: ``[][A]_vars``."""


@dataclass(frozen=True, repr=False)
class Property(_OptionalPredicateClause):
    """Temporal property over infinite behaviors: ``PROPERTY P``."""


@dataclass(frozen=True, repr=False)
class Fairness(_OptionalPredicateClause):
    """Fairness assumption conjoined to ``Spec`` (``WF`` / ``SF``)."""


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
    """Precondition or action enabling guard."""


@dataclass(frozen=True, repr=False)
class Ensures(_PredicateClause):
    """Postcondition (``old(e)`` is pre-state, bare ``e`` is post-state, ``result`` is return value)."""


@dataclass(frozen=True, repr=False)
class Preserves(_PredicateClause):
    """Inductive preservation obligation across an operation: ``P(s) => P(s')``."""


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
    """Next-state value ``value'`` inside an ``Action`` or ``ActionInvariant``."""
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
# Model configuration, finite domains, and symbolic values
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


@dataclass(frozen=True)
class Domain(Generic[_T_co]):
    """Finite value domain for model checking (e.g. ``Domain.range(0, 10)``)."""

    elements: Collection[_T_co]

    @classmethod
    def range(cls, start: int, stop: int) -> Domain[int]:
        """Inclusive integer interval ``start..stop`` (matching TLA+ ``start..stop``)."""
        return Domain(range(start, stop + 1))

    @classmethod
    def values(cls, *items: _T) -> Domain[_T]:
        """Explicit finite set of values."""
        return Domain(items)

    @classmethod
    def boolean(cls) -> Domain[bool]:
        """TLA+ ``BOOLEAN`` domain ``{FALSE, TRUE}``."""
        return Domain((False, True))

    def __iter__(self) -> Iterator[_T_co]:
        return iter(self.elements)

    def __len__(self) -> int:
        return len(self.elements)

    def __contains__(self, item: object) -> bool:
        return item in self.elements

    def __repr__(self) -> str:
        if isinstance(self.elements, range) and self.elements.step == 1:
            return f"Domain.range({self.elements.start}, {self.elements.stop - 1})"
        if (
            isinstance(self.elements, tuple)
            and len(self.elements) == 2
            and self.elements[0] is False
            and self.elements[1] is True
        ):
            return "Domain.boolean()"
        args = ", ".join(repr(x) for x in self.elements)
        return f"Domain.values({args})"


def _empty_dict() -> dict[Any, Any]:
    return {}


@dataclass(frozen=True)
class Model:
    """Declarative model configuration (Python equivalent of a TLA+ ``.cfg``).

    ``spec`` may be a specification class, ``Protocol``, generic alias,
    external ``Annotated[...]`` alias, module, or standalone function.
    """

    spec: Any
    constants: Mapping[str, Any] = field(default_factory=_empty_dict)
    domains: Mapping[Any, Iterable[Any]] = field(default_factory=_empty_dict)
    init: Optional[Union[str, Callable[..., Any]]] = None
    actions: Optional[Sequence[Union[str, Callable[..., Any]]]] = None
    invariants: Optional[Sequence[Union[str, Callable[..., Any]]]] = None
    properties: Optional[Sequence[Union[str, Callable[..., Any]]]] = None
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
    "Constant",
    "Domain",
    "Ensures",
    "Fairness",
    "Ghost",
    "Init",
    "Invariant",
    "Model",
    "ModelValue",
    "Modifies",
    "Preserves",
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
