"""Passive reflection over Temporal type annotations and specification metadata.

These helpers inspect annotations using Python's standard ``typing`` machinery
(``get_origin``, ``get_args``, ``get_type_hints``). They do not parse source
ASTs, compile TLA+, check models, or execute user predicates.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from types import MappingProxyType, ModuleType
from typing import (
    Annotated,
    Any,
    Optional,
    Union,
    get_args,
    get_origin,
    get_type_hints,
)

from ._contracts import (
    Ensures,
    Modifies,
    Refines,
    Requires,
    StrongFairness,
    Unchanged,
    WeakFairness,
    Where,
)
from ._types import Role

TemporalMetadata = Union[
    Role,
    Where,
    Requires,
    Ensures,
    Modifies,
    Unchanged,
    WeakFairness,
    StrongFairness,
]

_TEMPORAL_TYPES = (
    Role,
    Where,
    Requires,
    Ensures,
    Modifies,
    Unchanged,
    WeakFairness,
    StrongFairness,
)

_FAIRNESS_TYPES = (WeakFairness, StrongFairness)

_FIELD_ROLES = {Role.CONST, Role.STATE, Role.GHOST}

_EMPTY_MAPPING: Mapping[str, Any] = MappingProxyType({})


def _empty_mapping() -> Mapping[str, Any]:
    return _EMPTY_MAPPING


def is_temporal_metadata(obj: Any) -> bool:
    """Return True if ``obj`` is a Temporal annotation metadata item."""
    return isinstance(obj, _TEMPORAL_TYPES)


def get_metadata(annotation: Any) -> tuple[TemporalMetadata, ...]:
    """Return the Temporal metadata items attached to ``annotation``."""
    if get_origin(annotation) is not Annotated:
        return ()
    return tuple(m for m in get_args(annotation)[1:] if is_temporal_metadata(m))


def get_role(annotation: Any) -> Optional[Role]:
    """Return the single ``Role`` attached to ``annotation``, or ``None``.

    Raises ``ValueError`` if conflicting ``Role`` markers are present.
    """
    roles = [m for m in get_metadata(annotation) if isinstance(m, Role)]
    if not roles:
        return None
    unique = dict.fromkeys(roles)
    if len(unique) > 1:
        names = ", ".join(r.name for r in unique)
        raise ValueError(f"Conflicting Temporal roles on annotation: {names}")
    return roles[0]


def strip_temporal(annotation: Any) -> Any:
    """Remove Temporal metadata from ``annotation``, preserving any other metadata."""
    if get_origin(annotation) is not Annotated:
        return annotation
    args = get_args(annotation)
    base = args[0]
    remaining = tuple(m for m in args[1:] if not is_temporal_metadata(m))
    if not remaining:
        return base
    return Annotated[(base, *remaining)]


def _extract_refines_target(annotation: Any) -> Optional[Any]:
    base = get_args(annotation)[0] if get_origin(annotation) is Annotated else annotation
    if base is Refines:
        return Any
    if get_origin(base) is Refines:
        args = get_args(base)
        return args[0] if args else Any
    return None


def _unwrap_callable(member: object) -> Optional[Callable[..., Any]]:
    if isinstance(member, property):
        return member.fget
    if isinstance(member, (staticmethod, classmethod)):
        fn: object = member.__dict__.get("__func__", getattr(member, "__func__", None))  # pyright: ignore[reportUnknownArgumentType]
        return fn if callable(fn) else None
    if isinstance(member, type):
        return None
    if callable(member):
        return member
    return None


@dataclass(frozen=True)
class FieldInfo:
    """Metadata extracted from a ``Const``, ``State``, or ``Ghost`` attribute."""

    name: str
    role: Role
    type: Any
    refinements: tuple[Where, ...] = ()


@dataclass(frozen=True)
class ContractInfo:
    """Metadata extracted from an annotated function or method."""

    role: Optional[Role] = None
    return_type: Any = Any
    requires: tuple[Requires, ...] = ()
    ensures: tuple[Ensures, ...] = ()
    modifies: tuple[Modifies, ...] = ()
    unchanged: tuple[Unchanged, ...] = ()
    fairness: tuple[Union[WeakFairness, StrongFairness], ...] = ()
    return_refinements: tuple[Where, ...] = ()
    param_refinements: Mapping[str, tuple[Where, ...]] = field(default_factory=_empty_mapping)
    refines: Optional[Any] = None

    @property
    def is_temporal(self) -> bool:
        """True if any Temporal declaration or contract clause is present."""
        return bool(
            self.role is not None
            or self.requires
            or self.ensures
            or self.modifies
            or self.unchanged
            or self.fairness
            or self.return_refinements
            or self.param_refinements
            or self.refines is not None
        )


@dataclass(frozen=True)
class SpecInfo:
    """Metadata extracted from a specification class, protocol, or module."""

    target: Any
    constants: Mapping[str, FieldInfo] = field(default_factory=_empty_mapping)
    state: Mapping[str, FieldInfo] = field(default_factory=_empty_mapping)
    ghost: Mapping[str, FieldInfo] = field(default_factory=_empty_mapping)
    assumptions: Mapping[str, ContractInfo] = field(default_factory=_empty_mapping)
    inits: Mapping[str, ContractInfo] = field(default_factory=_empty_mapping)
    actions: Mapping[str, ContractInfo] = field(default_factory=_empty_mapping)
    pure: Mapping[str, ContractInfo] = field(default_factory=_empty_mapping)
    invariants: Mapping[str, ContractInfo] = field(default_factory=_empty_mapping)
    action_invariants: Mapping[str, ContractInfo] = field(default_factory=_empty_mapping)
    properties: Mapping[str, ContractInfo] = field(default_factory=_empty_mapping)
    fairness: Mapping[str, ContractInfo] = field(default_factory=_empty_mapping)
    refinements: Mapping[str, Any] = field(default_factory=_empty_mapping)


def get_contract(
    func: Any,
    *,
    globalns: Optional[dict[str, Any]] = None,
    localns: Optional[Mapping[str, Any]] = None,
) -> ContractInfo:
    """Extract Temporal contract metadata from a function, method, or descriptor."""
    fn = _unwrap_callable(func)
    if fn is None:
        raise TypeError(f"Expected a callable or property, got {type(func).__name__}")
    hints = get_type_hints(fn, globalns=globalns, localns=localns, include_extras=True)

    param_refinements: dict[str, tuple[Where, ...]] = {}
    for param, ann in hints.items():
        if param == "return":
            continue
        wheres = tuple(m for m in get_metadata(ann) if isinstance(m, Where))
        if wheres:
            param_refinements[param] = wheres

    if "return" not in hints:
        return ContractInfo(param_refinements=MappingProxyType(param_refinements))

    ret_ann = hints["return"]
    meta = get_metadata(ret_ann)
    role = get_role(ret_ann)
    if role in _FIELD_ROLES:
        raise ValueError(
            f"Field role {role.name} cannot be used as a callable return annotation"
        )
    refines = _extract_refines_target(ret_ann)

    return ContractInfo(
        role=role,
        return_type=strip_temporal(ret_ann),
        requires=tuple(m for m in meta if isinstance(m, Requires)),
        ensures=tuple(m for m in meta if isinstance(m, Ensures)),
        modifies=tuple(m for m in meta if isinstance(m, Modifies)),
        unchanged=tuple(m for m in meta if isinstance(m, Unchanged)),
        fairness=tuple(m for m in meta if isinstance(m, _FAIRNESS_TYPES)),
        return_refinements=tuple(m for m in meta if isinstance(m, Where)),
        param_refinements=MappingProxyType(param_refinements),
        refines=refines,
    )


def _iter_members(target: Union[type[Any], ModuleType]) -> list[tuple[str, Any]]:
    if isinstance(target, ModuleType):
        return [
            (name, value)
            for name, value in vars(target).items()
            if not name.startswith("__")
            and getattr(value, "__module__", None) == target.__name__
        ]
    seen: dict[str, Any] = {}
    for cls in reversed(target.__mro__):
        if cls is object or cls.__module__ == "typing":
            continue
        for name, value in cls.__dict__.items():
            if name.startswith("__") and name.endswith("__"):
                continue
            seen[name] = value
    return list(seen.items())


def get_spec(
    target: Any,
    *,
    globalns: Optional[dict[str, Any]] = None,
    localns: Optional[Mapping[str, Any]] = None,
) -> SpecInfo:
    """Extract all Temporal declarations from a class, protocol, generic alias, or module."""
    origin = get_origin(target)
    resolved = origin if isinstance(origin, type) else target
    if not isinstance(resolved, (type, ModuleType)):
        raise TypeError(
            f"Expected a class, protocol, or module, got {type(target).__name__}"
        )

    constants: dict[str, FieldInfo] = {}
    state: dict[str, FieldInfo] = {}
    ghost: dict[str, FieldInfo] = {}

    attr_hints = get_type_hints(
        resolved, globalns=globalns, localns=localns, include_extras=True
    )
    for name, ann in attr_hints.items():
        role = get_role(ann)
        if role is None:
            continue
        if role not in _FIELD_ROLES:
            raise ValueError(
                f"Callable role {role.name} cannot be used on attribute {name!r}"
            )
        wheres = tuple(m for m in get_metadata(ann) if isinstance(m, Where))
        info = FieldInfo(
            name=name, role=role, type=strip_temporal(ann), refinements=wheres
        )
        if role is Role.CONST:
            constants[name] = info
        elif role is Role.STATE:
            state[name] = info
        else:
            ghost[name] = info

    buckets: dict[Role, dict[str, ContractInfo]] = {
        Role.ASSUME: {},
        Role.INIT: {},
        Role.ACTION: {},
        Role.PURE: {},
        Role.INVARIANT: {},
        Role.ACTION_INVARIANT: {},
        Role.PROPERTY: {},
        Role.FAIRNESS: {},
    }
    refinements: dict[str, Any] = {}

    for name, member in _iter_members(resolved):
        if _unwrap_callable(member) is None:
            continue
        contract = get_contract(member, globalns=globalns, localns=localns)
        if contract.role is not None:
            buckets[contract.role][name] = contract
        if contract.refines is not None:
            refinements[name] = contract.refines

    return SpecInfo(
        target=target,
        constants=MappingProxyType(constants),
        state=MappingProxyType(state),
        ghost=MappingProxyType(ghost),
        assumptions=MappingProxyType(buckets[Role.ASSUME]),
        inits=MappingProxyType(buckets[Role.INIT]),
        actions=MappingProxyType(buckets[Role.ACTION]),
        pure=MappingProxyType(buckets[Role.PURE]),
        invariants=MappingProxyType(buckets[Role.INVARIANT]),
        action_invariants=MappingProxyType(buckets[Role.ACTION_INVARIANT]),
        properties=MappingProxyType(buckets[Role.PROPERTY]),
        fairness=MappingProxyType(buckets[Role.FAIRNESS]),
        refinements=MappingProxyType(refinements),
    )
