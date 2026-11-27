"""Contract, framing, fairness, and refinement metadata declarations.

All clauses are passive, immutable metadata objects intended for use inside
``typing.Annotated[...]`` (or as a ``Refines[...]`` return annotation).
Predicates are never executed by Temporal.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Generic, Optional, TypeVar

_S_co = TypeVar("_S_co", covariant=True)


def _check_predicate(kind: str, predicate: Any) -> None:
    if not callable(predicate):
        raise TypeError(f"{kind} predicate must be callable, got {type(predicate).__name__}")


def _check_description(kind: str, description: Any) -> None:
    if description is not None and not isinstance(description, str):
        raise TypeError(
            f"{kind} description must be a str or None, got {type(description).__name__}"
        )


def _validate_variables(kind: str, variables: tuple[Any, ...]) -> tuple[str, ...]:
    checked: list[str] = []
    for var in variables:
        if not isinstance(var, str):
            raise TypeError(
                f"{kind} variable names must be str, got {type(var).__name__}"
            )
        if not var.isidentifier():
            raise ValueError(
                f"{kind} variable name must be a valid Python identifier, got {var!r}"
            )
        checked.append(var)
    return tuple(checked)


@dataclass(frozen=True)
class Where:
    """Refinement predicate on a type: ``{x \\in T : predicate(x)}``.

    Always takes a single argument representing the annotated value. Its
    verification obligation follows its position:
    - On ``Const[T]``: constant assumption (``ASSUME``).
    - On ``State[T]`` / ``Ghost[T]``: state invariant (``TypeOK``).
    - On a parameter: precondition.
    - On a return type: postcondition.
    """

    predicate: Callable[[Any], bool]
    description: Optional[str] = None

    def __post_init__(self) -> None:
        _check_predicate("Where", self.predicate)
        _check_description("Where", self.description)


@dataclass(frozen=True)
class Requires:
    """Precondition or enabling guard on a function or action."""

    predicate: Callable[..., bool]
    description: Optional[str] = None

    def __post_init__(self) -> None:
        _check_predicate("Requires", self.predicate)
        _check_description("Requires", self.description)


@dataclass(frozen=True)
class Ensures:
    """Postcondition on a function or action.

    Inside ``Ensures``, state expressions refer to the post-state (``x'``),
    ``old(expr)`` refers to the pre-state (``x``), and ``result`` refers to
    the return value.
    """

    predicate: Callable[..., bool]
    description: Optional[str] = None

    def __post_init__(self) -> None:
        _check_predicate("Ensures", self.predicate)
        _check_description("Ensures", self.description)


@dataclass(frozen=True)
class Modifies:
    """Frame clause: only the named state variables may change.

    Every other state variable of the specification is implicitly
    ``UNCHANGED``. An empty ``Modifies()`` forbids all state changes.
    """

    variables: tuple[str, ...]

    def __init__(self, *variables: str) -> None:
        object.__setattr__(self, "variables", _validate_variables("Modifies", variables))


@dataclass(frozen=True)
class Unchanged:
    """Frame clause: the named state variables must remain ``UNCHANGED``."""

    variables: tuple[str, ...]

    def __init__(self, *variables: str) -> None:
        object.__setattr__(self, "variables", _validate_variables("Unchanged", variables))


@dataclass(frozen=True)
class WeakFairness:
    """Weak fairness metadata on an action: ``WF_v(action)``.

    When ``variables`` is empty, ``v`` defaults to the tuple of all state
    variables of the enclosing specification.
    """

    variables: tuple[str, ...]

    def __init__(self, *variables: str) -> None:
        object.__setattr__(
            self, "variables", _validate_variables("WeakFairness", variables)
        )


@dataclass(frozen=True)
class StrongFairness:
    """Strong fairness metadata on an action: ``SF_v(action)``.

    When ``variables`` is empty, ``v`` defaults to the tuple of all state
    variables of the enclosing specification.
    """

    variables: tuple[str, ...]

    def __init__(self, *variables: str) -> None:
        object.__setattr__(
            self, "variables", _validate_variables("StrongFairness", variables)
        )


class Refines(Generic[_S_co]):
    """Refinement mapping to an abstract specification (TLA+ ``INSTANCE ... WITH``).

    Used as the return annotation of a refinement method::

        def as_queue(self) -> Refines[BoundedQueue[T]]:
            return Refines(capacity=self.capacity, items=...)

    An empty ``Refines()`` denotes an identity mapping where concrete
    variables share the names of the abstract specification's variables.
    """

    __slots__ = ("_mapping",)
    _mapping: Mapping[str, Any]

    def __init__(self, **mapping: Any) -> None:
        object.__setattr__(self, "_mapping", MappingProxyType(dict(mapping)))

    @property
    def mapping(self) -> Mapping[str, Any]:
        return self._mapping

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __delattr__(self, name: str) -> None:
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __eq__(self, other: object) -> bool:
        if type(self) is not type(other):
            return NotImplemented
        assert isinstance(other, Refines)
        return dict(self._mapping) == dict(other._mapping)

    def __repr__(self) -> str:
        items = ", ".join(f"{k}={v!r}" for k, v in self._mapping.items())
        return f"Refines({items})"
