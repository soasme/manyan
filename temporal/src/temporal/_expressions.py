"""TLA+ logical, action, and temporal expression primitives.

Single-state logical primitives (``implies``, ``iff``, ``choose``) have exact
runtime semantics in Python so single-state predicates (such as ``Init`` and
``Invariant``) remain directly executable if called in tests.

Two-state and temporal primitives (``old``, ``prime``, ``unchanged``,
``enabled``, ``always``, ``eventually``, ``leads_to``, ``weak_fairness``,
``strong_fairness``) have no single-state runtime meaning: they are analysed
statically by verification tools and raise ``SpecificationError`` if invoked
directly at runtime.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable
from typing import Any, Optional, TypeVar

_T = TypeVar("_T")


class SpecificationError(RuntimeError):
    """Raised when a non-executable temporal or two-state primitive is called at runtime."""


def _spec_only(name: str) -> SpecificationError:
    return SpecificationError(
        f"{name}() is a declarative specification primitive and cannot be evaluated at runtime"
    )


# ---------------------------------------------------------------------------
# Executable single-state logical primitives
# ---------------------------------------------------------------------------


def implies(antecedent: bool, consequent: bool) -> bool:
    """Logical implication: ``antecedent => consequent``."""
    return (not antecedent) or bool(consequent)


def iff(left: bool, right: bool) -> bool:
    """Logical equivalence: ``left <=> right``."""
    return bool(left) == bool(right)


def choose(
    domain: Iterable[_T],
    predicate: Optional[Callable[[_T], bool]] = None,
) -> _T:
    """Hilbert's choice operator: ``CHOOSE x \\in domain : predicate(x)``.

    When ``predicate`` is omitted, corresponds to ``CHOOSE x \\in domain : TRUE``.
    Raises ``ValueError`` if no element of ``domain`` satisfies ``predicate``.
    """
    if predicate is not None and not callable(predicate):
        raise TypeError(
            f"choose() predicate must be callable or None, got {type(predicate).__name__}"
        )
    saw_any = False
    for element in domain:
        saw_any = True
        if predicate is None or predicate(element):
            return element
    if not saw_any:
        raise ValueError("choose() domain is empty")
    raise ValueError("choose() found no element satisfying predicate")


# ---------------------------------------------------------------------------
# Declarative two-state (action-level) primitives
# ---------------------------------------------------------------------------


def old(value: _T) -> _T:
    """Pre-state value of ``value`` inside an ``Ensures`` postcondition."""
    raise _spec_only("old")


def prime(value: _T) -> _T:
    """Next-state value ``value'`` inside a declarative ``Action`` or ``ActionInvariant``."""
    raise _spec_only("prime")


def unchanged(*values: Any) -> bool:
    """Stuttering predicate ``UNCHANGED <<v1, v2, ...>>``."""
    raise _spec_only("unchanged")


def enabled(action: Any) -> bool:
    """Enabling predicate ``ENABLED action``."""
    raise _spec_only("enabled")


# ---------------------------------------------------------------------------
# Declarative temporal-level primitives
# ---------------------------------------------------------------------------


def always(formula: bool) -> bool:
    """Temporal safety operator ``[]formula`` (henceforth / box)."""
    raise _spec_only("always")


def eventually(formula: bool) -> bool:
    """Temporal liveness operator ``<>formula`` (eventually / diamond)."""
    raise _spec_only("eventually")


def leads_to(cause: bool, effect: bool) -> bool:
    """Temporal leads-to operator ``cause ~> effect`` (``[](cause => <>effect)``)."""
    raise _spec_only("leads_to")


def weak_fairness(action: Any, *, on: Any = None) -> bool:
    """Weak fairness operator ``WF_on(action)``.

    When ``on`` is omitted, the subscript defaults to all state variables of
    the enclosing specification.
    """
    raise _spec_only("weak_fairness")


def strong_fairness(action: Any, *, on: Any = None) -> bool:
    """Strong fairness operator ``SF_on(action)``.

    When ``on`` is omitted, the subscript defaults to all state variables of
    the enclosing specification.
    """
    raise _spec_only("strong_fairness")
