"""Model configuration declarations, uninterpreted model values, and symmetry sets."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass, field
from types import MappingProxyType, ModuleType
from typing import (
    Any,
    Generic,
    Optional,
    TypeVar,
    cast,
    get_origin,
    overload,
)

_T_co = TypeVar("_T_co", covariant=True)
_S = TypeVar("_S")

_EMPTY_MAPPING: Mapping[Any, Any] = MappingProxyType({})


def _empty_mapping() -> Mapping[Any, Any]:
    return _EMPTY_MAPPING


def _check_name(name: object) -> str:
    if not isinstance(name, str):
        raise TypeError(f"ModelValue name must be str, got {type(name).__name__}")
    if not name or not name.strip():
        raise ValueError("ModelValue name must be a non-empty string")
    return name


class ModelValue:
    """An uninterpreted TLA+ model value.

    Two model values are equal if and only if they have the exact same type
    and name. Subclass ``ModelValue`` to define disjoint uninterpreted sorts::

        class Proc(ModelValue): ...
        class Msg(ModelValue): ...
        assert Proc("a") != Msg("a")
        assert Proc("a") != "a"

    Model values are immutable, hashable, and unordered.
    """

    __slots__ = ("_name",)
    _name: str

    def __init__(self, name: str) -> None:
        object.__setattr__(self, "_name", _check_name(name))

    @property
    def name(self) -> str:
        return self._name

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __delattr__(self, name: str) -> None:
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __eq__(self, other: object) -> bool:
        if type(self) is not type(other):
            return False
        assert isinstance(other, ModelValue)
        return self._name == other._name

    def __hash__(self) -> int:
        return hash((type(self), self._name))

    def __str__(self) -> str:
        return self._name

    def __repr__(self) -> str:
        return f"{type(self).__name__}({self._name!r})"

    def __reduce__(self) -> tuple[type[ModelValue], tuple[str]]:
        return (type(self), (self._name,))


class Symmetry(frozenset[_T_co]):
    """An immutable finite set marked as symmetric (TLA+ ``SYMMETRY``).

    Because ``Symmetry`` subclasses ``frozenset``, it can be passed directly
    anywhere a ``frozenset`` is expected while signalling to verification tools
    that permutations of its elements are behaviourally equivalent.
    """

    def __repr__(self) -> str:
        if not self:
            return f"{type(self).__name__}()"
        return f"{type(self).__name__}({set(self)!r})"

    def __reduce__(self) -> tuple[type[Symmetry[_T_co]], tuple[tuple[_T_co, ...]]]:
        return (type(self), (tuple(self),))


def _is_valid_spec(spec: Any) -> bool:
    if isinstance(spec, (type, ModuleType)):
        return True
    return isinstance(get_origin(spec), type)


def _freeze_domain(domain: object) -> Any:
    if isinstance(domain, (Symmetry, frozenset, tuple, range)):
        return cast(object, domain)
    if isinstance(domain, set):
        return frozenset(cast("set[object]", domain))
    if isinstance(domain, Iterable) and not isinstance(domain, (str, bytes)):
        return tuple(cast("Iterable[object]", domain))
    raise TypeError(
        f"Model domain must be a finite iterable (not str/bytes), got {type(domain).__name__}"
    )


def _freeze_callables(
    name: str, items: object
) -> Optional[tuple[Callable[..., Any], ...]]:
    if items is None:
        return None
    if isinstance(items, (str, bytes)) or not isinstance(items, Iterable):
        raise TypeError(f"Model {name} must be an iterable of callables or None")
    result: list[Callable[..., Any]] = []
    for item in cast("Iterable[object]", items):
        if not callable(item):
            raise TypeError(
                f"Model {name} entries must be callable, got {type(item).__name__}"
            )
        result.append(item)
    return tuple(result)


def _freeze_constants(constants: object) -> Mapping[str, Any]:
    if not isinstance(constants, Mapping):
        raise TypeError(
            f"Model constants must be a mapping, got {type(constants).__name__}"
        )
    checked: dict[str, Any] = {}
    for key, value in cast("Mapping[object, object]", constants).items():
        if not isinstance(key, str) or not key.isidentifier():
            raise ValueError(
                f"Model constant name must be a valid Python identifier, got {key!r}"
            )
        checked[key] = value
    return MappingProxyType(checked)


def _freeze_domains(domains: object) -> Mapping[Any, Any]:
    if not isinstance(domains, Mapping):
        raise TypeError(
            f"Model domains must be a mapping, got {type(domains).__name__}"
        )
    return MappingProxyType(
        {
            k: _freeze_domain(v)
            for k, v in cast("Mapping[object, object]", domains).items()
        }
    )


def _freeze_symmetries(symmetry: object) -> tuple[Symmetry[Any], ...]:
    if isinstance(symmetry, (str, bytes)) or not isinstance(symmetry, Iterable):
        raise TypeError("Model symmetry must be an iterable of Symmetry sets")
    sym_list: list[Symmetry[Any]] = []
    for item in cast("Iterable[object]", symmetry):
        if not isinstance(item, Symmetry):
            raise TypeError(
                f"Model symmetry entries must be Symmetry instances, got {type(item).__name__}"
            )
        sym_list.append(cast("Symmetry[object]", item))
    return tuple(sym_list)


def _check_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"Model {name} must be bool, got {type(value).__name__}")
    return value


def _check_optional_callable(name: str, fn: object) -> None:
    if fn is not None and not callable(fn):
        raise TypeError(f"Model {name} must be callable or None, got {type(fn).__name__}")


@dataclass(frozen=True, init=False)
class Model(Generic[_S]):
    """Declarative model-checking configuration (Python equivalent of a TLA+ ``.cfg``).

    A ``Model`` binds a specification's constants, finite type/parameter
    domains, symmetry sets, constraints, views, and checked properties without
    executing any model checker.
    """

    spec: Any
    constants: Mapping[str, Any] = field(default_factory=_empty_mapping)
    domains: Mapping[Any, Any] = field(default_factory=_empty_mapping)
    init: Optional[Callable[..., Any]] = None
    actions: Optional[tuple[Callable[..., Any], ...]] = None
    invariants: Optional[tuple[Callable[..., Any], ...]] = None
    properties: Optional[tuple[Callable[..., Any], ...]] = None
    state_constraint: Optional[Callable[..., bool]] = None
    action_constraint: Optional[Callable[..., bool]] = None
    symmetry: tuple[Symmetry[Any], ...] = ()
    view: Optional[Callable[..., Any]] = None
    alias: Optional[Callable[..., Any]] = None
    postcondition: Optional[Callable[..., bool]] = None
    check_deadlock: bool = True

    @overload
    def __init__(
        self,
        spec: type[_S],
        *,
        constants: Mapping[str, Any] = ...,
        domains: Mapping[Any, Iterable[Any]] = ...,
        init: Optional[Callable[..., Any]] = None,
        actions: Optional[Iterable[Callable[..., Any]]] = None,
        invariants: Optional[Iterable[Callable[..., Any]]] = None,
        properties: Optional[Iterable[Callable[..., Any]]] = None,
        state_constraint: Optional[Callable[..., bool]] = None,
        action_constraint: Optional[Callable[..., bool]] = None,
        symmetry: Iterable[Symmetry[Any]] = ...,
        view: Optional[Callable[..., Any]] = None,
        alias: Optional[Callable[..., Any]] = None,
        postcondition: Optional[Callable[..., bool]] = None,
        check_deadlock: bool = True,
    ) -> None: ...

    @overload
    def __init__(
        self: Model[Any],
        spec: ModuleType,
        *,
        constants: Mapping[str, Any] = ...,
        domains: Mapping[Any, Iterable[Any]] = ...,
        init: Optional[Callable[..., Any]] = None,
        actions: Optional[Iterable[Callable[..., Any]]] = None,
        invariants: Optional[Iterable[Callable[..., Any]]] = None,
        properties: Optional[Iterable[Callable[..., Any]]] = None,
        state_constraint: Optional[Callable[..., bool]] = None,
        action_constraint: Optional[Callable[..., bool]] = None,
        symmetry: Iterable[Symmetry[Any]] = ...,
        view: Optional[Callable[..., Any]] = None,
        alias: Optional[Callable[..., Any]] = None,
        postcondition: Optional[Callable[..., bool]] = None,
        check_deadlock: bool = True,
    ) -> None: ...

    def __init__(
        self,
        spec: Any,
        *,
        constants: Mapping[str, Any] = _EMPTY_MAPPING,
        domains: Mapping[Any, Iterable[Any]] = _EMPTY_MAPPING,
        init: Optional[Callable[..., Any]] = None,
        actions: Optional[Iterable[Callable[..., Any]]] = None,
        invariants: Optional[Iterable[Callable[..., Any]]] = None,
        properties: Optional[Iterable[Callable[..., Any]]] = None,
        state_constraint: Optional[Callable[..., bool]] = None,
        action_constraint: Optional[Callable[..., bool]] = None,
        symmetry: Iterable[Symmetry[Any]] = (),
        view: Optional[Callable[..., Any]] = None,
        alias: Optional[Callable[..., Any]] = None,
        postcondition: Optional[Callable[..., bool]] = None,
        check_deadlock: bool = True,
    ) -> None:
        if not _is_valid_spec(spec):
            raise TypeError(
                f"Model spec must be a class, protocol, or module, got {type(spec).__name__}"
            )
        _check_optional_callable("init", init)
        _check_optional_callable("state_constraint", state_constraint)
        _check_optional_callable("action_constraint", action_constraint)
        _check_optional_callable("view", view)
        _check_optional_callable("alias", alias)
        _check_optional_callable("postcondition", postcondition)

        object.__setattr__(self, "spec", spec)
        object.__setattr__(self, "constants", _freeze_constants(constants))
        object.__setattr__(self, "domains", _freeze_domains(domains))
        object.__setattr__(self, "init", init)
        object.__setattr__(self, "actions", _freeze_callables("actions", actions))
        object.__setattr__(
            self, "invariants", _freeze_callables("invariants", invariants)
        )
        object.__setattr__(
            self, "properties", _freeze_callables("properties", properties)
        )
        object.__setattr__(self, "state_constraint", state_constraint)
        object.__setattr__(self, "action_constraint", action_constraint)
        object.__setattr__(self, "symmetry", _freeze_symmetries(symmetry))
        object.__setattr__(self, "view", view)
        object.__setattr__(self, "alias", alias)
        object.__setattr__(self, "postcondition", postcondition)
        object.__setattr__(
            self, "check_deadlock", _check_bool("check_deadlock", check_deadlock)
        )

    @property
    def symmetries(self) -> tuple[Symmetry[Any], ...]:
        """All unique ``Symmetry`` sets declared explicitly or via constants/domains."""
        seen: list[Symmetry[Any]] = []
        candidates: tuple[Any, ...] = (
            *self.symmetry,
            *self.constants.values(),
            *self.domains.values(),
        )
        for candidate in candidates:
            if isinstance(candidate, Symmetry) and candidate not in seen:
                seen.append(cast("Symmetry[object]", candidate))
        return tuple(seen)
