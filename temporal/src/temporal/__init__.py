"""Temporal: behavioural specification declarations for Python, grounded in TLA+.

Temporal is a pure declaration library with zero runtime dependencies. It
provides type annotations, contract clauses, TLA+ expression primitives,
model configuration objects, and passive metadata inspection. Verification
is performed externally by tools such as Manyan.
"""

from __future__ import annotations

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
from ._expressions import (
    SpecificationError,
    always,
    choose,
    enabled,
    eventually,
    iff,
    implies,
    leads_to,
    old,
    prime,
    strong_fairness,
    unchanged,
    weak_fairness,
)
from ._inspect import (
    ContractInfo,
    FieldInfo,
    SpecInfo,
    TemporalMetadata,
    get_contract,
    get_metadata,
    get_role,
    get_spec,
    is_temporal_metadata,
    strip_temporal,
)
from ._model import Model, ModelValue, Symmetry
from ._types import (
    Action,
    ActionInvariant,
    Assume,
    Const,
    Fairness,
    Ghost,
    Init,
    Invariant,
    Property,
    Pure,
    Role,
    State,
)

__version__ = "0.1.0"

__all__ = [
    "Action",
    "ActionInvariant",
    "Assume",
    "Const",
    "ContractInfo",
    "Ensures",
    "Fairness",
    "FieldInfo",
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
    "SpecInfo",
    "SpecificationError",
    "State",
    "StrongFairness",
    "Symmetry",
    "TemporalMetadata",
    "Unchanged",
    "WeakFairness",
    "Where",
    "__version__",
    "always",
    "choose",
    "enabled",
    "eventually",
    "get_contract",
    "get_metadata",
    "get_role",
    "get_spec",
    "iff",
    "implies",
    "is_temporal_metadata",
    "leads_to",
    "old",
    "prime",
    "strip_temporal",
    "strong_fairness",
    "unchanged",
    "weak_fairness",
]
