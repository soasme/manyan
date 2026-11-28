"""Compile Python source annotated with `temporal` into TLA+ models for Manyan.

This module analyses Python source purely via `ast` without importing or
executing user code. It extracts Temporal declarations (`State`, `Constant`,
`Ghost`, `Pure`, `Assume`, `Init`, `Action`, `Invariant`, `ActionInvariant`,
`Property`, `Fairness`, `Where`, `Requires`, `Ensures`, `Preserves`,
`Modifies`, `Unchanged`, `WeakFairness`, `StrongFairness`, `Refines`,
`ModelValue`, `Symmetry`, `Domain`, `Model`), compiles them into TLA+ modules
and `.cfg` configurations, and hands them to Manyan for model checking.
"""
import ast
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple, Union


class TemporalCompileError(ValueError):
    """Raised when a Temporal declaration cannot be translated to TLA+."""


# ---------------------------------------------------------------------------
# Internal IR
# ---------------------------------------------------------------------------


@dataclass
class _TypeInfo:
    kind: str  # "int", "bool", "str", "seq", "set", "map", "model", "any"
    elem: Optional["_TypeInfo"] = None
    key: Optional["_TypeInfo"] = None
    val: Optional["_TypeInfo"] = None
    name: Optional[str] = None
    literals: Optional[Tuple[Any, ...]] = None
    wheres: List[ast.expr] = field(default_factory=list)
    nullable: bool = False


@dataclass
class _FieldDecl:
    name: str
    role: str  # "constant", "state", "ghost"
    type_info: _TypeInfo
    default: Optional[ast.expr] = None


@dataclass
class _ClauseDecl:
    name: str
    kind: str  # "assume", "init", "invariant", "action_invariant", "property", "fairness"
    expr: Optional[ast.expr] = None
    func: Optional[ast.FunctionDef] = None


@dataclass
class _ActionDecl:
    name: str
    params: List[Tuple[str, _TypeInfo]] = field(default_factory=list)
    return_type: _TypeInfo = field(default_factory=lambda: _TypeInfo("any"))
    requires: List[ast.expr] = field(default_factory=list)
    ensures: List[ast.expr] = field(default_factory=list)
    preserves: List[ast.expr] = field(default_factory=list)
    action_preds: List[ast.expr] = field(default_factory=list)
    modifies: List[Tuple[str, ...]] = field(default_factory=list)
    unchanged: List[Tuple[str, ...]] = field(default_factory=list)
    weak_fairness: List[Tuple[str, ...]] = field(default_factory=list)
    strong_fairness: List[Tuple[str, ...]] = field(default_factory=list)
    func: Optional[ast.FunctionDef] = None
    has_body: bool = False
    is_bool_action: bool = False


@dataclass
class _PureDecl:
    name: str
    params: List[Tuple[str, _TypeInfo]]
    return_type: _TypeInfo
    func: ast.FunctionDef
    is_property: bool = False
    requires: List[ast.expr] = field(default_factory=list)
    ensures: List[ast.expr] = field(default_factory=list)


@dataclass
class _RefineDecl:
    name: str
    target_name: str
    mapping: Dict[str, ast.expr]
    receiver: str


@dataclass
class _SpecDecl:
    name: str
    bases: List[str] = field(default_factory=list)
    type_params: List[str] = field(default_factory=list)
    is_protocol: bool = False
    constants: Dict[str, _FieldDecl] = field(default_factory=dict)
    states: Dict[str, _FieldDecl] = field(default_factory=dict)
    ghosts: Dict[str, _FieldDecl] = field(default_factory=dict)
    assumptions: List[_ClauseDecl] = field(default_factory=list)
    inits: List[_ClauseDecl] = field(default_factory=list)
    invariants: List[_ClauseDecl] = field(default_factory=list)
    action_invariants: List[_ClauseDecl] = field(default_factory=list)
    properties: List[_ClauseDecl] = field(default_factory=list)
    fairness: List[_ClauseDecl] = field(default_factory=list)
    actions: Dict[str, _ActionDecl] = field(default_factory=dict)
    pure_ops: Dict[str, _PureDecl] = field(default_factory=dict)
    refinements: List[_RefineDecl] = field(default_factory=list)


@dataclass(frozen=True)
class _ModelValueRef:
    sort: str
    name: str


@dataclass(frozen=True)
class _SymmetryVal:
    items: Tuple[Any, ...]


@dataclass(frozen=True)
class _DomainVal:
    kind: str  # "range", "values", "boolean"
    start: int = 0
    stop: int = 0
    items: Tuple[Any, ...] = ()


@dataclass
class _ModelDecl:
    name: str
    spec_name: str
    constants: Dict[str, Any] = field(default_factory=dict)
    domains: Dict[str, Any] = field(default_factory=dict)
    init_override: Optional[str] = None
    actions_override: Optional[List[str]] = None
    invariants_override: Optional[List[str]] = None
    properties_override: Optional[List[str]] = None
    state_constraint: Optional[ast.expr] = None
    action_constraint: Optional[ast.expr] = None
    symmetry: List[_SymmetryVal] = field(default_factory=list)
    view: Optional[ast.expr] = None
    alias: Optional[ast.expr] = None
    postcondition: Optional[ast.expr] = None
    check_deadlock: bool = True


@dataclass
class CompiledModel:
    """A compiled TLA+ module and `.cfg` generated from Python source."""

    name: str
    module_name: str
    tla: str
    cfg: str
    source: Optional[str] = None
    spec_name: Optional[str] = None
    model_name: Optional[str] = None


# ---------------------------------------------------------------------------
# AST Helpers
# ---------------------------------------------------------------------------


def _dotted_name(node: ast.expr) -> Optional[str]:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        parent = _dotted_name(node.value)
        return f"{parent}.{node.attr}" if parent else None
    return None


def _is_ellipsis_body(body: List[ast.stmt]) -> bool:
    stmts = [
        s for s in body
        if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and isinstance(s.value.value, str))
    ]
    if not stmts:
        return True
    if len(stmts) == 1:
        s = stmts[0]
        if isinstance(s, ast.Pass):
            return True
        if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and s.value.value is Ellipsis:
            return True
    return False


def _sanitize_ident(name: str) -> str:
    clean = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not clean or clean[0].isdigit():
        clean = "M_" + clean
    return clean


def _tla_string(s: str) -> str:
    esc = (
        s.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\t", "\\t")
        .replace("\r", "\\r")
    )
    return f'"{esc}"'


# ---------------------------------------------------------------------------
# Module Parser: Extract Temporal Declarations from Python AST
# ---------------------------------------------------------------------------


class _ModuleExtractor:
    def __init__(self, tree: ast.Module, source_path: Optional[str] = None) -> None:
        self.tree = tree
        self.source_path = source_path
        self.temporal_aliases: Dict[str, str] = {}
        self.temporal_modules: Set[str] = set()
        self.model_value_sorts: Set[str] = {"ModelValue"}
        self.type_aliases: Dict[str, _TypeInfo] = {}
        self.typevars: Set[str] = set()
        self.env: Dict[str, Any] = {}
        self.specs: Dict[str, _SpecDecl] = {}
        self.models: List[_ModelDecl] = []
        self.functions: List[_PureDecl] = []

    def _temporal_name(self, node: ast.expr) -> Optional[str]:
        if isinstance(node, ast.Name):
            return self.temporal_aliases.get(node.id)
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            if node.value.id in self.temporal_modules:
                return node.attr
        return None

    def _is_annotated(self, node: ast.expr) -> bool:
        return isinstance(node, ast.Subscript) and _dotted_name(node.value) in ("Annotated", "typing.Annotated")

    def _is_classvar(self, node: ast.expr) -> bool:
        return isinstance(node, ast.Subscript) and _dotted_name(node.value) in ("ClassVar", "typing.ClassVar")

    def _unwrap_classvar(self, node: ast.expr) -> ast.expr:
        while self._is_classvar(node):
            assert isinstance(node, ast.Subscript)
            node = node.slice
        return node

    def _annotated_parts(self, node: ast.expr) -> Tuple[ast.expr, List[ast.expr]]:
        """Unwrap nested Annotated[base, m1, m2, ...] into (base, [metadata...])."""
        node = self._unwrap_classvar(node)
        if not self._is_annotated(node):
            return node, []
        assert isinstance(node, ast.Subscript)
        sl = node.slice
        if isinstance(sl, ast.Tuple) and len(sl.elts) >= 2:
            inner_base, inner_meta = self._annotated_parts(sl.elts[0])
            return inner_base, inner_meta + list(sl.elts[1:])
        return node, []

    def _resolve_type(self, node: Optional[ast.expr]) -> _TypeInfo:
        if node is None:
            return _TypeInfo("any")
        node = self._unwrap_classvar(node)
        base, meta = self._annotated_parts(node)
        wheres: List[ast.expr] = []
        for m in meta:
            if isinstance(m, ast.Call) and self._temporal_name(m.func) == "Where" and m.args:
                wheres.append(m.args[0])

        info = self._resolve_bare_type(base)
        if wheres:
            return _TypeInfo(
                kind=info.kind,
                elem=info.elem,
                key=info.key,
                val=info.val,
                name=info.name,
                literals=info.literals,
                wheres=list(info.wheres) + wheres,
                nullable=info.nullable,
            )
        return info

    def _resolve_bare_type(self, node: ast.expr) -> _TypeInfo:
        if isinstance(node, ast.Subscript):
            tname = self._temporal_name(node.value)
            if tname in ("State", "Constant", "Ghost", "Pure"):
                return self._resolve_type(node.slice)
            head = _dotted_name(node.value) or ""
            if head in ("Optional", "typing.Optional"):
                inner = self._resolve_type(node.slice)
                return _TypeInfo(
                    kind=inner.kind,
                    elem=inner.elem,
                    key=inner.key,
                    val=inner.val,
                    name=inner.name,
                    literals=inner.literals,
                    wheres=list(inner.wheres),
                    nullable=True,
                )
            if head in ("Union", "typing.Union") and isinstance(node.slice, ast.Tuple):
                non_none = [
                    e for e in node.slice.elts
                    if not (isinstance(e, ast.Constant) and e.value is None)
                ]
                has_none = len(non_none) < len(node.slice.elts)
                if len(non_none) == 1:
                    inner = self._resolve_type(non_none[0])
                    return _TypeInfo(
                        kind=inner.kind,
                        elem=inner.elem,
                        key=inner.key,
                        val=inner.val,
                        name=inner.name,
                        literals=inner.literals,
                        wheres=list(inner.wheres),
                        nullable=inner.nullable or has_none,
                    )
                return _TypeInfo("any", nullable=has_none)
            if head in ("Literal", "typing.Literal"):
                elts = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
                lits = tuple(self._eval_const(e) for e in elts)
                kind = "str" if lits and all(isinstance(v, str) for v in lits) else "any"
                return _TypeInfo(kind, literals=lits)
            if head in ("tuple", "Tuple", "typing.Tuple", "list", "List", "Sequence", "typing.Sequence"):
                elem = node.slice.elts[0] if isinstance(node.slice, ast.Tuple) else node.slice
                return _TypeInfo("seq", elem=self._resolve_type(elem))
            if head in ("frozenset", "set", "Set", "FrozenSet", "typing.FrozenSet", "typing.Set"):
                return _TypeInfo("set", elem=self._resolve_type(node.slice))
            if head in ("dict", "Dict", "Mapping", "typing.Dict", "typing.Mapping"):
                if isinstance(node.slice, ast.Tuple) and len(node.slice.elts) == 2:
                    return _TypeInfo(
                        "map",
                        key=self._resolve_type(node.slice.elts[0]),
                        val=self._resolve_type(node.slice.elts[1]),
                    )
                return _TypeInfo("map")
            return _TypeInfo("any", name=head)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            left_none = isinstance(node.left, ast.Constant) and node.left.value is None
            right_none = isinstance(node.right, ast.Constant) and node.right.value is None
            if left_none:
                inner = self._resolve_type(node.right)
                return _TypeInfo(inner.kind, inner.elem, inner.key, inner.val, inner.name, inner.literals, list(inner.wheres), nullable=True)
            if right_none:
                inner = self._resolve_type(node.left)
                return _TypeInfo(inner.kind, inner.elem, inner.key, inner.val, inner.name, inner.literals, list(inner.wheres), nullable=True)
            return _TypeInfo("any")
        if isinstance(node, ast.Name):
            if node.id in self.type_aliases:
                return self.type_aliases[node.id]
            if node.id == "int":
                return _TypeInfo("int", name="int")
            if node.id == "bool":
                return _TypeInfo("bool", name="bool")
            if node.id == "str":
                return _TypeInfo("str", name="str")
            if node.id in self.model_value_sorts:
                return _TypeInfo("model", name=node.id)
            if node.id in self.typevars:
                return _TypeInfo("any", name=node.id)
            return _TypeInfo("any", name=node.id)
        if isinstance(node, ast.Constant) and node.value is None:
            return _TypeInfo("none")
        return _TypeInfo("any")

    def _eval_const(self, node: ast.expr) -> Any:
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -self._eval_const(node.operand)
        if isinstance(node, ast.Tuple):
            return tuple(self._eval_const(e) for e in node.elts)
        if isinstance(node, ast.List):
            return [self._eval_const(e) for e in node.elts]
        if isinstance(node, ast.Set):
            return frozenset(self._eval_const(e) for e in node.elts)
        if isinstance(node, ast.Dict):
            return {self._eval_const(k): self._eval_const(v) for k, v in zip(node.keys, node.values) if k is not None}
        if isinstance(node, ast.Name):
            if node.id in self.env:
                return self.env[node.id]
            if node.id in self.specs or node.id in self.model_value_sorts or node.id in self.typevars or node.id in ("int", "bool", "str"):
                return node.id
            raise TemporalCompileError(f"Unknown constant reference: {node.id!r}")
        if isinstance(node, ast.Call):
            tname = self._temporal_name(node.func)
            if tname == "ModelValue" and len(node.args) == 1:
                return _ModelValueRef("ModelValue", str(self._eval_const(node.args[0])))
            if tname == "Symmetry":
                if not node.args:
                    return _SymmetryVal(())
                val = self._eval_const(node.args[0])
                return _SymmetryVal(tuple(val))
            if isinstance(node.func, ast.Name) and node.func.id in self.model_value_sorts and len(node.args) == 1:
                return _ModelValueRef(node.func.id, str(self._eval_const(node.args[0])))
            if isinstance(node.func, ast.Name) and node.func.id == "frozenset":
                return frozenset(self._eval_const(node.args[0])) if node.args else frozenset()
            if isinstance(node.func, ast.Name) and node.func.id == "range":
                args = [int(self._eval_const(a)) for a in node.args]
                r = range(*args)
                return _DomainVal("range", r.start, r.stop - 1) if r.step == 1 else _DomainVal("values", items=tuple(r))
            if isinstance(node.func, ast.Attribute) and self._temporal_name(node.func.value) == "Domain":
                method = node.func.attr
                if method == "range" and len(node.args) == 2:
                    return _DomainVal("range", int(self._eval_const(node.args[0])), int(self._eval_const(node.args[1])))
                if method == "values":
                    return _DomainVal("values", items=tuple(self._eval_const(a) for a in node.args))
                if method == "boolean":
                    return _DomainVal("boolean")
        raise TemporalCompileError(f"Unsupported constant expression: {ast.dump(node)}")

    def extract(self) -> None:
        # Pass 1: imports
        for stmt in self.tree.body:
            if isinstance(stmt, ast.ImportFrom) and stmt.module == "temporal":
                for alias in stmt.names:
                    self.temporal_aliases[alias.asname or alias.name] = alias.name
            elif isinstance(stmt, ast.Import):
                for alias in stmt.names:
                    if alias.name == "temporal":
                        self.temporal_modules.add(alias.asname or alias.name)

        # Pass 2: classes, aliases, values, functions, models
        for stmt in self.tree.body:
            if isinstance(stmt, ast.ClassDef):
                self._extract_class(stmt)
            elif isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
                self._extract_assign(stmt.targets[0].id, stmt.value)
            elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name) and stmt.value is not None:
                self._extract_assign(stmt.target.id, stmt.value)
            elif isinstance(stmt, ast.FunctionDef):
                fn = self._extract_standalone_function(stmt)
                if fn is not None:
                    self.functions.append(fn)

    def _extract_assign(self, name: str, value: ast.expr) -> None:
        if isinstance(value, ast.Call):
            if _dotted_name(value.func) in ("TypeVar", "typing.TypeVar"):
                self.typevars.add(name)
                return
            if self._temporal_name(value.func) == "Model":
                self.models.append(self._extract_model(name, value))
                return
        # Check external Annotated[Spec, ...] alias
        if self._is_annotated(value):
            base, meta = self._annotated_parts(value)
            if isinstance(base, ast.Name) and base.id in self.specs:
                self._extract_annotated_spec_alias(name, base.id, meta)
                return
            self.type_aliases[name] = self._resolve_type(value)
            return
        if isinstance(value, ast.Subscript) and _dotted_name(value.value) in ("Literal", "typing.Literal"):
            self.type_aliases[name] = self._resolve_type(value)
            return
        try:
            self.env[name] = self._eval_const(value)
        except TemporalCompileError:
            pass

    def _extract_annotated_spec_alias(self, name: str, base_name: str, meta: List[ast.expr]) -> None:
        base = self.specs[base_name]
        derived = _SpecDecl(
            name=name,
            bases=[base_name],
            type_params=list(base.type_params),
            constants=dict(base.constants),
            states=dict(base.states),
            ghosts=dict(base.ghosts),
            assumptions=list(base.assumptions),
            inits=list(base.inits),
            invariants=list(base.invariants),
            action_invariants=list(base.action_invariants),
            properties=list(base.properties),
            fairness=list(base.fairness),
            actions=dict(base.actions),
            pure_ops=dict(base.pure_ops),
            refinements=list(base.refinements),
        )
        for idx, m in enumerate(meta):
            if isinstance(m, ast.Call):
                cname = self._temporal_name(m.func)
                if cname in ("Assume", "Init", "Invariant", "ActionInvariant", "Property", "Fairness"):
                    pred = m.args[0] if m.args else None
                    kind = {
                        "Assume": "assume",
                        "Init": "init",
                        "Invariant": "invariant",
                        "ActionInvariant": "action_invariant",
                        "Property": "property",
                        "Fairness": "fairness",
                    }[cname]
                    decl = _ClauseDecl(f"{kind}_{idx}", kind, expr=pred)
                    getattr(derived, {
                        "assume": "assumptions",
                        "init": "inits",
                        "invariant": "invariants",
                        "action_invariant": "action_invariants",
                        "property": "properties",
                        "fairness": "fairness",
                    }[kind]).append(decl)
        self.specs[name] = derived

    def _extract_class(self, cls: ast.ClassDef) -> None:
        # Check ModelValue subclass
        for b in cls.bases:
            if self._temporal_name(b) == "ModelValue" or (isinstance(b, ast.Name) and b.id in self.model_value_sorts):
                self.model_value_sorts.add(cls.name)
                return

        spec = _SpecDecl(name=cls.name)
        for b in cls.bases:
            if isinstance(b, ast.Name):
                if b.id == "Protocol":
                    spec.is_protocol = True
                elif b.id in self.specs:
                    spec.bases.append(b.id)
            elif isinstance(b, ast.Subscript):
                head = _dotted_name(b.value) or ""
                if head in ("Protocol", "typing.Protocol"):
                    spec.is_protocol = True
                elif head in ("Generic", "typing.Generic"):
                    pass
                elif isinstance(b.value, ast.Name) and b.value.id in self.specs:
                    spec.bases.append(b.value.id)
                elts = b.slice.elts if isinstance(b.slice, ast.Tuple) else [b.slice]
                for e in elts:
                    if isinstance(e, ast.Name) and e.id in self.typevars and e.id not in spec.type_params:
                        spec.type_params.append(e.id)

        # Inherit declarations from base specs in same module
        for base_name in spec.bases:
            base = self.specs[base_name]
            spec.constants.update(base.constants)
            spec.states.update(base.states)
            spec.ghosts.update(base.ghosts)
            spec.assumptions.extend(base.assumptions)
            spec.inits.extend(base.inits)
            spec.invariants.extend(base.invariants)
            spec.action_invariants.extend(base.action_invariants)
            spec.properties.extend(base.properties)
            spec.fairness.extend(base.fairness)
            spec.actions.update(base.actions)
            spec.pure_ops.update(base.pure_ops)

        has_temporal = bool(spec.bases)
        for stmt in cls.body:
            if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                if self._extract_class_attr(spec, stmt):
                    has_temporal = True
            elif isinstance(stmt, ast.FunctionDef):
                if self._extract_class_method(spec, stmt):
                    has_temporal = True

        if has_temporal:
            self.specs[cls.name] = spec

    def _extract_class_attr(self, spec: _SpecDecl, stmt: ast.AnnAssign) -> bool:
        assert isinstance(stmt.target, ast.Name)
        name = stmt.target.id
        ann = self._unwrap_classvar(stmt.annotation)

        # Direct Constant[T] / State[T] / Ghost[T]
        if isinstance(ann, ast.Subscript):
            tname = self._temporal_name(ann.value)
            if tname in ("Constant", "State", "Ghost"):
                role = tname.lower()
                info = self._resolve_type(ann.slice)
                decl = _FieldDecl(name=name, role=role, type_info=info, default=stmt.value)
                getattr(spec, {"constant": "constants", "state": "states", "ghost": "ghosts"}[role])[name] = decl
                return True

        # Annotated[T, ...]
        base, meta = self._annotated_parts(ann)
        if not meta:
            return False

        # Check if base is Constant/State/Ghost
        if isinstance(base, ast.Subscript):
            tname = self._temporal_name(base.value)
            if tname in ("Constant", "State", "Ghost"):
                role = tname.lower()
                info = self._resolve_type(ann)
                decl = _FieldDecl(name=name, role=role, type_info=info, default=stmt.value)
                getattr(spec, {"constant": "constants", "state": "states", "ghost": "ghosts"}[role])[name] = decl
                return True

        found = False
        action_decl: Optional[_ActionDecl] = None
        for m in meta:
            if not isinstance(m, ast.Call):
                continue
            cname = self._temporal_name(m.func)
            pred = m.args[0] if m.args else None
            if cname in ("Assume", "Init", "Invariant", "ActionInvariant", "Property", "Fairness"):
                kind = {
                    "Assume": "assume",
                    "Init": "init",
                    "Invariant": "invariant",
                    "ActionInvariant": "action_invariant",
                    "Property": "property",
                    "Fairness": "fairness",
                }[cname]
                bucket = {
                    "assume": spec.assumptions,
                    "init": spec.inits,
                    "invariant": spec.invariants,
                    "action_invariant": spec.action_invariants,
                    "property": spec.properties,
                    "fairness": spec.fairness,
                }[kind]
                bucket.append(_ClauseDecl(name=name, kind=kind, expr=pred))
                found = True
            elif cname == "Action":
                action_decl = action_decl or _ActionDecl(name=name, is_bool_action=True)
                if pred is not None:
                    action_decl.action_preds.append(pred)
                found = True
            elif cname in ("Requires", "Ensures", "Preserves", "Modifies", "Unchanged", "WeakFairness", "StrongFairness"):
                action_decl = action_decl or _ActionDecl(name=name, is_bool_action=True)
                self._add_action_clause(action_decl, cname, m)
                found = True

        if action_decl is not None:
            spec.actions[name] = action_decl
        return found

    def _add_action_clause(self, action: _ActionDecl, cname: str, call: ast.Call) -> None:
        if cname == "Requires" and call.args:
            action.requires.append(call.args[0])
        elif cname == "Ensures" and call.args:
            action.ensures.append(call.args[0])
        elif cname == "Preserves" and call.args:
            action.preserves.append(call.args[0])
        elif cname == "Action":
            if call.args:
                action.action_preds.append(call.args[0])
        elif cname in ("Modifies", "Unchanged", "WeakFairness", "StrongFairness"):
            vnames = tuple(str(self._eval_const(a)) for a in call.args)
            target = {
                "Modifies": action.modifies,
                "Unchanged": action.unchanged,
                "WeakFairness": action.weak_fairness,
                "StrongFairness": action.strong_fairness,
            }[cname]
            target.append(vnames)

    def _extract_class_method(self, spec: _SpecDecl, fn: ast.FunctionDef) -> bool:
        if fn.returns is None:
            return False

        is_prop = any(isinstance(d, ast.Name) and d.id == "property" for d in fn.decorator_list)
        ret_base, ret_meta = self._annotated_parts(fn.returns)

        # Refines[AbstractSpec]
        if isinstance(ret_base, ast.Subscript) and self._temporal_name(ret_base.value) == "Refines":
            target_node = ret_base.slice
            target_name = target_node.value.id if isinstance(target_node, ast.Subscript) and isinstance(target_node.value, ast.Name) else (
                target_node.id if isinstance(target_node, ast.Name) else ""
            )
            mapping: Dict[str, ast.expr] = {}
            receiver = fn.args.args[0].arg if fn.args.args else "self"
            for stmt in fn.body:
                if isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.Call) and self._temporal_name(stmt.value.func) == "Refines":
                    for kw in stmt.value.keywords:
                        if kw.arg is not None:
                            mapping[kw.arg] = kw.value
            spec.refinements.append(_RefineDecl(name=fn.name, target_name=target_name, mapping=mapping, receiver=receiver))
            return True

        # Pure[T]
        if isinstance(ret_base, ast.Subscript) and self._temporal_name(ret_base.value) == "Pure":
            params = [(a.arg, self._resolve_type(a.annotation)) for a in fn.args.args[1:]]
            spec.pure_ops[fn.name] = _PureDecl(
                name=fn.name,
                params=params,
                return_type=self._resolve_type(ret_base.slice),
                func=fn,
                is_property=is_prop,
            )
            return True

        if not ret_meta:
            return False

        # System predicate method (Assume / Init / Invariant / ActionInvariant / Property / Fairness)
        for m in ret_meta:
            if isinstance(m, ast.Call):
                cname = self._temporal_name(m.func)
                if cname in ("Assume", "Init", "Invariant", "ActionInvariant", "Property", "Fairness"):
                    kind = {
                        "Assume": "assume",
                        "Init": "init",
                        "Invariant": "invariant",
                        "ActionInvariant": "action_invariant",
                        "Property": "property",
                        "Fairness": "fairness",
                    }[cname]
                    bucket = {
                        "assume": spec.assumptions,
                        "init": spec.inits,
                        "invariant": spec.invariants,
                        "action_invariant": spec.action_invariants,
                        "property": spec.properties,
                        "fairness": spec.fairness,
                    }[kind]
                    pred = m.args[0] if m.args else None
                    bucket.append(_ClauseDecl(name=fn.name, kind=kind, expr=pred, func=fn))
                    return True

        # Action / contract method
        has_action_meta = any(
            isinstance(m, ast.Call)
            and self._temporal_name(m.func) in ("Action", "Requires", "Ensures", "Preserves", "Modifies", "Unchanged", "WeakFairness", "StrongFairness")
            for m in ret_meta
        )
        if not has_action_meta:
            return False

        params = [(a.arg, self._resolve_type(a.annotation)) for a in fn.args.args[1:]]
        ret_type = self._resolve_type(fn.returns)
        receiver = fn.args.args[0].arg if fn.args.args else "self"
        mutates_state = any(
            (
                isinstance(s, ast.Assign)
                and any(isinstance(t, ast.Attribute) and isinstance(t.value, ast.Name) and t.value.id == receiver for t in s.targets)
            )
            or (
                isinstance(s, ast.AugAssign)
                and isinstance(s.target, ast.Attribute)
                and isinstance(s.target.value, ast.Name)
                and s.target.value.id == receiver
            )
            for s in ast.walk(fn)
        )
        action = _ActionDecl(
            name=fn.name,
            params=params,
            return_type=ret_type,
            func=fn,
            has_body=not _is_ellipsis_body(fn.body),
            is_bool_action=(
                ret_type.kind == "bool"
                and not mutates_state
                and not any(
                    isinstance(m, ast.Call) and self._temporal_name(m.func) == "Ensures"
                    for m in ret_meta
                )
            ),
        )
        for m in ret_meta:
            if isinstance(m, ast.Call):
                cname = self._temporal_name(m.func)
                if cname in ("Action", "Requires", "Ensures", "Preserves", "Modifies", "Unchanged", "WeakFairness", "StrongFairness"):
                    self._add_action_clause(action, cname, m)
        spec.actions[fn.name] = action
        return True

    def _extract_standalone_function(self, fn: ast.FunctionDef) -> Optional[_PureDecl]:
        if fn.returns is None:
            return None
        ret_base, ret_meta = self._annotated_parts(fn.returns)
        is_pure = isinstance(ret_base, ast.Subscript) and self._temporal_name(ret_base.value) == "Pure"
        requires: List[ast.expr] = []
        ensures: List[ast.expr] = []
        for m in ret_meta:
            if isinstance(m, ast.Call):
                cname = self._temporal_name(m.func)
                if cname == "Requires" and m.args:
                    requires.append(m.args[0])
                elif cname == "Ensures" and m.args:
                    ensures.append(m.args[0])
        if not (is_pure or requires or ensures):
            return None
        params = [(a.arg, self._resolve_type(a.annotation)) for a in fn.args.args]
        ret_type = self._resolve_type(fn.returns)
        return _PureDecl(
            name=fn.name,
            params=params,
            return_type=ret_type,
            func=fn,
            requires=requires,
            ensures=ensures,
        )

    def _extract_model(self, name: str, call: ast.Call) -> _ModelDecl:
        if not call.args:
            raise TemporalCompileError(f"Model {name!r} requires a specification argument")
        spec_arg = call.args[0]
        if isinstance(spec_arg, ast.Subscript) and isinstance(spec_arg.value, ast.Name):
            spec_name = spec_arg.value.id
        elif isinstance(spec_arg, ast.Name):
            spec_name = spec_arg.id
        else:
            raise TemporalCompileError(f"Unsupported Model spec target in {name!r}")

        model = _ModelDecl(name=name, spec_name=spec_name)
        for kw in call.keywords:
            if kw.arg == "constants":
                val = self._eval_const(kw.value)
                if isinstance(val, dict):
                    model.constants.update(val)
            elif kw.arg == "domains":
                if isinstance(kw.value, ast.Dict):
                    for k_node, v_node in zip(kw.value.keys, kw.value.values):
                        if k_node is None:
                            continue
                        if isinstance(k_node, ast.Constant) and isinstance(k_node.value, str):
                            k = k_node.value
                        elif isinstance(k_node, ast.Name):
                            k = k_node.id
                        else:
                            k = str(self._eval_const(k_node))
                        model.domains[k] = self._eval_const(v_node)
            elif kw.arg == "check_deadlock":
                model.check_deadlock = bool(self._eval_const(kw.value))
            elif kw.arg == "state_constraint":
                model.state_constraint = kw.value
            elif kw.arg == "action_constraint":
                model.action_constraint = kw.value
            elif kw.arg == "view":
                model.view = kw.value
            elif kw.arg == "alias":
                model.alias = kw.value
            elif kw.arg == "postcondition":
                model.postcondition = kw.value
            elif kw.arg == "symmetry":
                val = self._eval_const(kw.value)
                for item in val:
                    if isinstance(item, _SymmetryVal):
                        model.symmetry.append(item)
            elif kw.arg in ("actions", "invariants", "properties"):
                items = kw.value.elts if isinstance(kw.value, (ast.Tuple, ast.List)) else []
                names = [e.attr if isinstance(e, ast.Attribute) else (e.id if isinstance(e, ast.Name) else "") for e in items]
                setattr(model, f"{kw.arg}_override", [n for n in names if n])
            elif kw.arg == "init":
                if isinstance(kw.value, ast.Attribute):
                    model.init_override = kw.value.attr
                elif isinstance(kw.value, ast.Name):
                    model.init_override = kw.value.id
        return model


# ---------------------------------------------------------------------------
# Expression Compiler: Python AST -> TLA+
# ---------------------------------------------------------------------------


class _ExprCompiler:
    def __init__(
        self,
        extractor: _ModuleExtractor,
        spec: Optional[_SpecDecl],
        var_types: Dict[str, _TypeInfo],
        receiver: Optional[str] = None,
        post_by_default: bool = False,
        param_map: Optional[Dict[str, str]] = None,
        state_subst: Optional[Dict[str, str]] = None,
        action_prefix: str = "",
        needs_helpers: Optional[Set[str]] = None,
    ) -> None:
        self.extractor = extractor
        self.spec = spec
        self.var_types = dict(var_types)
        self.receiver = receiver
        self.post_by_default = post_by_default
        self.param_map = dict(param_map or {})
        self.state_subst = dict(state_subst or {})
        self.action_prefix = action_prefix
        self.needs_helpers = needs_helpers if needs_helpers is not None else set()

    def _tname(self, node: ast.expr) -> Optional[str]:
        return self.extractor._temporal_name(node)

    def _infer_kind(self, node: ast.expr) -> str:
        if isinstance(node, ast.Constant):
            if isinstance(node.value, bool):
                return "bool"
            if isinstance(node.value, int):
                return "int"
            if isinstance(node.value, str):
                return "str"
            return "none"
        if isinstance(node, (ast.Set, ast.SetComp)):
            return "set"
        if isinstance(node, (ast.Tuple, ast.List)):
            return "seq"
        if isinstance(node, (ast.Dict, ast.DictComp)):
            return "map"
        if isinstance(node, ast.Name):
            info = self.var_types.get(node.id)
            return info.kind if info else "any"
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == self.receiver:
            info = self.var_types.get(node.attr)
            return info.kind if info else "any"
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                if node.func.id in ("frozenset", "set"):
                    return "set"
                if node.func.id in ("tuple", "list"):
                    return "seq"
                if node.func.id in ("len", "sum", "min", "max", "abs"):
                    return "int"
                if node.func.id == "range":
                    return "set"
            if self._tname(node.func) in ("prime", "old") and node.args:
                return self._infer_kind(node.args[0])
        if isinstance(node, ast.Subscript):
            if isinstance(node.slice, ast.Slice):
                return "seq"
            return "any"
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.BitOr, ast.BitAnd)):
            return "set"
        return "any"

    def _state_ref(self, attr: str, primed: bool) -> str:
        if attr in self.state_subst:
            expr = self.state_subst[attr]
            return f"({expr})'" if primed else expr
        if self.spec and attr in self.spec.constants:
            return attr
        if self.spec and attr in self.spec.pure_ops and self.spec.pure_ops[attr].is_property:
            return f"{attr}'" if primed else attr
        return f"{attr}'" if primed else attr

    def compile(self, node: ast.expr, *, primed: Optional[bool] = None) -> str:
        use_prime = self.post_by_default if primed is None else primed

        if isinstance(node, ast.Constant):
            if node.value is True:
                return "TRUE"
            if node.value is False:
                return "FALSE"
            if node.value is None:
                self.needs_helpers.add("NONE")
                return "NONE"
            if isinstance(node.value, int):
                return str(node.value)
            if isinstance(node.value, str):
                return _tla_string(node.value)
            raise TemporalCompileError(f"Unsupported literal: {node.value!r}")

        if isinstance(node, ast.Name):
            if node.id in self.param_map:
                return self.param_map[node.id]
            if self.spec and (node.id in self.spec.states or node.id in self.spec.ghosts or node.id in self.spec.constants):
                return self._state_ref(node.id, use_prime)
            return node.id

        if isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Name) and node.value.id == self.receiver:
                return self._state_ref(node.attr, use_prime)
            base = self.compile(node.value, primed=use_prime)
            return f"{base}.{node.attr}"

        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                return f"(~({self.compile(node.operand, primed=use_prime)}))"
            if isinstance(node.op, ast.USub):
                return f"(-({self.compile(node.operand, primed=use_prime)}))"
            if isinstance(node.op, ast.UAdd):
                return self.compile(node.operand, primed=use_prime)
            raise TemporalCompileError(f"Unsupported unary op: {type(node.op).__name__}")

        if isinstance(node, ast.BoolOp):
            op = " /\\ " if isinstance(node.op, ast.And) else " \\/ "
            return "(" + op.join(self.compile(v, primed=use_prime) for v in node.values) + ")"

        if isinstance(node, ast.BinOp):
            lk = self._infer_kind(node.left)
            rk = self._infer_kind(node.right)
            left = self.compile(node.left, primed=use_prime)
            right = self.compile(node.right, primed=use_prime)
            if isinstance(node.op, ast.Add):
                if lk == "seq" or rk == "seq":
                    self.needs_helpers.add("Sequences")
                    return f"({left} \\o {right})"
                return f"({left} + {right})"
            if isinstance(node.op, ast.Sub):
                if lk == "set" or rk == "set":
                    return f"({left} \\ {right})"
                return f"({left} - {right})"
            if isinstance(node.op, ast.Mult):
                # Pattern: (val,) * n -> [i \in 1..n |-> val]
                if isinstance(node.left, ast.Tuple) and len(node.left.elts) == 1:
                    val_tla = self.compile(node.left.elts[0], primed=use_prime)
                    return f"[_i \\in 1..({right}) |-> {val_tla}]"
                return f"({left} * {right})"
            if isinstance(node.op, ast.FloorDiv):
                return f"({left} \\div {right})"
            if isinstance(node.op, ast.Mod):
                return f"({left} % {right})"
            if isinstance(node.op, ast.Pow):
                return f"({left} ^ {right})"
            if isinstance(node.op, ast.BitOr):
                return f"({left} \\cup {right})"
            if isinstance(node.op, ast.BitAnd):
                return f"({left} \\cap {right})"
            raise TemporalCompileError(f"Unsupported binary op: {type(node.op).__name__}")

        if isinstance(node, ast.Compare):
            parts: List[str] = []
            cur = node.left
            for op, nxt in zip(node.ops, node.comparators):
                lk = self._infer_kind(cur)
                rk = self._infer_kind(nxt)
                l_str = self.compile(cur, primed=use_prime)
                r_str = self.compile(nxt, primed=use_prime)
                if isinstance(op, (ast.Eq, ast.Is)):
                    parts.append(f"({l_str} = {r_str})")
                elif isinstance(op, (ast.NotEq, ast.IsNot)):
                    parts.append(f"({l_str} # {r_str})")
                elif isinstance(op, ast.Lt):
                    if lk == "set" or rk == "set":
                        parts.append(f"(({l_str} \\subseteq {r_str}) /\\ ({l_str} # {r_str}))")
                    else:
                        parts.append(f"({l_str} < {r_str})")
                elif isinstance(op, ast.LtE):
                    if lk == "set" or rk == "set":
                        parts.append(f"({l_str} \\subseteq {r_str})")
                    else:
                        parts.append(f"({l_str} <= {r_str})")
                elif isinstance(op, ast.Gt):
                    parts.append(f"({l_str} > {r_str})")
                elif isinstance(op, ast.GtE):
                    parts.append(f"({l_str} >= {r_str})")
                elif isinstance(op, ast.In):
                    if rk == "seq":
                        self.needs_helpers.add("Sequences")
                        parts.append(f"(\\E _idx \\in 1..Len({r_str}) : {r_str}[_idx] = {l_str})")
                    else:
                        parts.append(f"({l_str} \\in {r_str})")
                elif isinstance(op, ast.NotIn):
                    if rk == "seq":
                        self.needs_helpers.add("Sequences")
                        parts.append(f"(~(\\E _idx \\in 1..Len({r_str}) : {r_str}[_idx] = {l_str}))")
                    else:
                        parts.append(f"({l_str} \\notin {r_str})")
                else:
                    raise TemporalCompileError(f"Unsupported comparison: {type(op).__name__}")
                cur = nxt
            return parts[0] if len(parts) == 1 else "(" + " /\\ ".join(parts) + ")"

        if isinstance(node, ast.IfExp):
            return (
                f"(IF {self.compile(node.test, primed=use_prime)} "
                f"THEN {self.compile(node.body, primed=use_prime)} "
                f"ELSE {self.compile(node.orelse, primed=use_prime)})"
            )

        if isinstance(node, (ast.Tuple, ast.List)):
            elts = ", ".join(self.compile(e, primed=use_prime) for e in node.elts)
            return f"<<{elts}>>"

        if isinstance(node, ast.Set):
            elts = ", ".join(self.compile(e, primed=use_prime) for e in node.elts)
            return "{" + elts + "}"

        if isinstance(node, ast.Dict):
            return self._compile_dict(node, use_prime)

        if isinstance(node, ast.DictComp):
            if len(node.generators) == 1 and isinstance(node.generators[0].target, ast.Name):
                gen = node.generators[0]
                v = gen.target.id
                dom = self.compile(gen.iter, primed=use_prime)
                val = self.compile(node.value, primed=use_prime)
                return f"[{v} \\in {dom} |-> {val}]"
            raise TemporalCompileError("Unsupported dict comprehension")

        if isinstance(node, ast.SetComp):
            if len(node.generators) == 1 and isinstance(node.generators[0].target, ast.Name):
                gen = node.generators[0]
                v = gen.target.id
                dom = self.compile(gen.iter, primed=use_prime)
                if gen.ifs and isinstance(node.elt, ast.Name) and node.elt.id == v:
                    cond = " /\\ ".join(self.compile(c, primed=use_prime) for c in gen.ifs)
                    return "{" + f"{v} \\in {dom} : {cond}" + "}"
                if not gen.ifs:
                    return "{" + f"{self.compile(node.elt, primed=use_prime)} : {v} \\in {dom}" + "}"
            raise TemporalCompileError("Unsupported set comprehension")

        if isinstance(node, ast.Subscript):
            return self._compile_subscript(node, use_prime)

        if isinstance(node, ast.Call):
            return self._compile_call(node, use_prime)

        raise TemporalCompileError(f"Unsupported Python expression in specification: {ast.dump(node)}")

    def _compile_dict(self, node: ast.Dict, use_prime: bool) -> str:
        # Handle {**base, k: v, ...} -> [base EXCEPT ![k] = v, ...]
        if node.keys and node.keys[0] is None:
            base = self.compile(node.values[0], primed=use_prime)
            updates = []
            for k, v in zip(node.keys[1:], node.values[1:]):
                if k is None:
                    raise TemporalCompileError("Multiple dict unpackings are not supported")
                updates.append(f"![{self.compile(k, primed=use_prime)}] = {self.compile(v, primed=use_prime)}")
            return f"[{base} EXCEPT " + ", ".join(updates) + "]"
        if not node.keys:
            return "[_k \\in {} |-> 0]"
        # Record literal with string keys
        if all(isinstance(k, ast.Constant) and isinstance(k.value, str) for k in node.keys):
            pairs = ", ".join(
                f"{k.value} |-> {self.compile(v, primed=use_prime)}"  # type: ignore[union-attr]
                for k, v in zip(node.keys, node.values)
            )
            return f"[{pairs}]"
        raise TemporalCompileError("Unsupported non-string dict literal")

    def _compile_subscript(self, node: ast.Subscript, use_prime: bool) -> str:
        obj_kind = self._infer_kind(node.value)
        obj = self.compile(node.value, primed=use_prime)
        if isinstance(node.slice, ast.Slice):
            self.needs_helpers.add("Sequences")
            lower = f"(({self.compile(node.slice.lower, primed=use_prime)}) + 1)" if node.slice.lower is not None else "1"
            upper = self.compile(node.slice.upper, primed=use_prime) if node.slice.upper is not None else f"Len({obj})"
            if node.slice.lower is not None and isinstance(node.slice.lower, ast.Constant) and node.slice.lower.value == 1 and node.slice.upper is None:
                return f"Tail({obj})"
            return f"SubSeq({obj}, {lower}, {upper})"
        if obj_kind == "map":
            return f"{obj}[{self.compile(node.slice, primed=use_prime)}]"
        # Sequence/tuple 0-based -> 1-based
        self.needs_helpers.add("Sequences")
        if isinstance(node.slice, ast.UnaryOp) and isinstance(node.slice.op, ast.USub) and isinstance(node.slice.operand, ast.Constant):
            k = int(node.slice.operand.value)
            return f"{obj}[Len({obj})]" if k == 1 else f"{obj}[(Len({obj}) - {k - 1})]"
        return f"{obj}[(({self.compile(node.slice, primed=use_prime)}) + 1)]"

    def _compile_call(self, node: ast.Call, use_prime: bool) -> str:
        tname = self._tname(node.func)
        if tname == "implies" and len(node.args) == 2:
            return f"({self.compile(node.args[0], primed=use_prime)} => {self.compile(node.args[1], primed=use_prime)})"
        if tname == "iff" and len(node.args) == 2:
            return f"({self.compile(node.args[0], primed=use_prime)} <=> {self.compile(node.args[1], primed=use_prime)})"
        if tname == "prime" and len(node.args) == 1:
            return self.compile(node.args[0], primed=True)
        if tname == "old" and len(node.args) == 1:
            return self.compile(node.args[0], primed=False)
        if tname == "unchanged":
            if len(node.args) == 1:
                return f"(UNCHANGED {self.compile(node.args[0], primed=False)})"
            vs = ", ".join(self.compile(a, primed=False) for a in node.args)
            return f"(UNCHANGED <<{vs}>>)"
        if tname == "always" and len(node.args) == 1:
            return f"([]{self.compile(node.args[0], primed=use_prime)})"
        if tname == "eventually" and len(node.args) == 1:
            return f"(<>{self.compile(node.args[0], primed=use_prime)})"
        if tname == "leads_to" and len(node.args) == 2:
            return f"({self.compile(node.args[0], primed=use_prime)} ~> {self.compile(node.args[1], primed=use_prime)})"
        if tname == "enabled" and len(node.args) == 1:
            return f"(ENABLED {self._compile_action_ref(node.args[0])})"
        if tname in ("weak_fairness", "strong_fairness") and len(node.args) == 1:
            prefix = "WF" if tname == "weak_fairness" else "SF"
            on_arg = next((kw.value for kw in node.keywords if kw.arg == "on"), None)
            sub = self.compile(on_arg, primed=False) if on_arg is not None else "_vars"
            return f"{prefix}_{sub}({self._compile_action_ref(node.args[0])})"
        if tname == "choose" and len(node.args) in (1, 2):
            dom = self.compile(node.args[0], primed=use_prime)
            if len(node.args) == 1:
                return f"(CHOOSE _x \\in {dom} : TRUE)"
            pred = node.args[1]
            if isinstance(pred, ast.Lambda) and len(pred.args.args) == 1:
                v = pred.args.args[0].arg
                return f"(CHOOSE {v} \\in {dom} : {self.compile(pred.body, primed=use_prime)})"
            raise TemporalCompileError("choose() predicate must be a 1-arg lambda")

        # Built-in functions
        if isinstance(node.func, ast.Name):
            fname = node.func.id
            if fname in ("all", "any") and len(node.args) == 1 and isinstance(node.args[0], ast.GeneratorExp):
                return self._compile_quantifier(fname, node.args[0], use_prime)
            if fname == "len" and len(node.args) == 1:
                k = self._infer_kind(node.args[0])
                arg = self.compile(node.args[0], primed=use_prime)
                if k == "set":
                    self.needs_helpers.add("FiniteSets")
                    return f"Cardinality({arg})"
                self.needs_helpers.add("Sequences")
                return f"Len({arg})"
            if fname == "sum" and len(node.args) == 1:
                self.needs_helpers.add("Sequences")
                self.needs_helpers.add("_Sum")
                return f"_Sum({self.compile(node.args[0], primed=use_prime)})"
            if fname == "min" and len(node.args) == 2:
                a = self.compile(node.args[0], primed=use_prime)
                b = self.compile(node.args[1], primed=use_prime)
                return f"(IF {a} < {b} THEN {a} ELSE {b})"
            if fname == "max" and len(node.args) == 2:
                a = self.compile(node.args[0], primed=use_prime)
                b = self.compile(node.args[1], primed=use_prime)
                return f"(IF {a} > {b} THEN {a} ELSE {b})"
            if fname == "abs" and len(node.args) == 1:
                a = self.compile(node.args[0], primed=use_prime)
                return f"(IF {a} < 0 THEN -({a}) ELSE {a})"
            if fname == "frozenset":
                return "{}" if not node.args else self.compile(node.args[0], primed=use_prime)
            if fname == "range":
                if len(node.args) == 1:
                    return f"(0..(({self.compile(node.args[0], primed=use_prime)}) - 1))"
                if len(node.args) == 2:
                    a = self.compile(node.args[0], primed=use_prime)
                    b = self.compile(node.args[1], primed=use_prime)
                    return f"(({a})..(({b}) - 1))"
            if fname == "tuple" and len(node.args) == 1 and isinstance(node.args[0], ast.GeneratorExp):
                return self._compile_tuple_gen(node.args[0], use_prime)

        # Method/action call on receiver: s.helper(x)
        if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and node.func.value.id == self.receiver:
            args = ", ".join(self.compile(a, primed=use_prime) for a in node.args)
            return f"{node.func.attr}({args})" if args else node.func.attr

        raise TemporalCompileError(f"Unsupported call in specification: {ast.dump(node)}")

    def _compile_action_ref(self, node: ast.expr) -> str:
        # s.acquire(p) -> acquire(p) | s.tm_commit() -> tm_commit | s.step -> step
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            aname = self.action_prefix + node.func.attr
            if not node.args:
                return aname
            args = ", ".join(self.compile(a, primed=False) for a in node.args)
            return f"{aname}({args})"
        if isinstance(node, ast.Attribute):
            return self.action_prefix + node.attr
        if isinstance(node, ast.Lambda):
            return self._compile_action_ref(node.body)
        return self.compile(node, primed=False)

    def _compile_quantifier(self, fname: str, gen: ast.GeneratorExp, use_prime: bool) -> str:
        q = "\\A" if fname == "all" else "\\E"
        reserved = set(self.var_types.keys())
        for m in self.extractor.models:
            _collect_model_values(m.constants, reserved)
            _collect_model_values(m.domains, reserved)
        renames: Dict[str, str] = {}
        bound_specs: List[Tuple[str, str, List[ast.expr]]] = []
        for comp in gen.generators:
            if not isinstance(comp.target, ast.Name):
                raise TemporalCompileError("Only simple variable targets are supported in quantifiers")
            orig = comp.target.id
            safe = f"_q_{orig}" if orig in reserved else orig
            renames[orig] = safe
            dom = self.compile(comp.iter, primed=use_prime)
            bound_specs.append((safe, dom, comp.ifs))
        sub = _ExprCompiler(
            self.extractor,
            self.spec,
            self.var_types,
            receiver=self.receiver,
            post_by_default=use_prime,
            param_map={**self.param_map, **renames},
            state_subst=self.state_subst,
            action_prefix=self.action_prefix,
            needs_helpers=self.needs_helpers,
        )
        body = sub.compile(gen.elt, primed=use_prime)
        for safe, dom, ifs in reversed(bound_specs):
            if ifs:
                cond = " /\\ ".join(sub.compile(c, primed=use_prime) for c in ifs)
                body = f"({cond} => {body})" if fname == "all" else f"({cond} /\\ {body})"
            body = f"({q} {safe} \\in {dom} : {body})"
        return body

    def _compile_tuple_gen(self, gen: ast.GeneratorExp, use_prime: bool) -> str:
        # tuple(expr for i in range(n)) -> [_i \in 1..n |-> expr(i -> _i - 1)]
        if len(gen.generators) == 1:
            comp = gen.generators[0]
            if (
                isinstance(comp.target, ast.Name)
                and not comp.ifs
                and isinstance(comp.iter, ast.Call)
                and isinstance(comp.iter.func, ast.Name)
                and comp.iter.func.id == "range"
                and len(comp.iter.args) == 1
            ):
                var = comp.target.id
                n_expr = self.compile(comp.iter.args[0], primed=use_prime)
                sub = _ExprCompiler(
                    self.extractor,
                    self.spec,
                    self.var_types,
                    receiver=self.receiver,
                    post_by_default=use_prime,
                    param_map={**self.param_map, var: "(_i - 1)"},
                    state_subst=self.state_subst,
                    action_prefix=self.action_prefix,
                    needs_helpers=self.needs_helpers,
                )
                return f"[_i \\in 1..({n_expr}) |-> {sub.compile(gen.elt, primed=use_prime)}]"
        raise TemporalCompileError("Unsupported tuple generator expression")


# ---------------------------------------------------------------------------
# Imperative Method & Pure Function Compiler
# ---------------------------------------------------------------------------


def _compile_imperative_body(
    fn: ast.FunctionDef,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: Dict[str, _TypeInfo],
    needs_helpers: Set[str],
) -> Tuple[Dict[str, str], Optional[str]]:
    """Symbolically execute a straight-line imperative method body to next-state expressions and return expr."""
    receiver = fn.args.args[0].arg if fn.args.args else "self"
    state_exprs: Dict[str, str] = {v: v for v in (*spec.states, *spec.ghosts)}
    locals_env: Dict[str, str] = {}
    local_list_copies: Dict[str, str] = {}  # local name -> underlying TLA+ sequence expr
    ret_expr: Optional[str] = None

    def mk_compiler() -> _ExprCompiler:
        return _ExprCompiler(
            extractor,
            spec,
            var_types,
            receiver=receiver,
            post_by_default=False,
            param_map=locals_env,
            state_subst=state_exprs,
            needs_helpers=needs_helpers,
        )

    def run_stmts(stmts: List[ast.stmt]) -> None:
        nonlocal ret_expr
        for s in stmts:
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and isinstance(s.value.value, str):
                continue
            if isinstance(s, (ast.Pass, ast.Assert)):
                continue
            if isinstance(s, ast.Return):
                if s.value is not None:
                    ret_expr = mk_compiler().compile(s.value)
                return
            if isinstance(s, ast.Assign) and len(s.targets) == 1:
                tgt = s.targets[0]
                if isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name) and tgt.value.id == receiver:
                    if isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Name) and s.value.func.id == "tuple" and len(s.value.args) == 1 and isinstance(s.value.args[0], ast.Name) and s.value.args[0].id in local_list_copies:
                        state_exprs[tgt.attr] = local_list_copies[s.value.args[0].id]
                    else:
                        state_exprs[tgt.attr] = mk_compiler().compile(s.value)
                elif isinstance(tgt, ast.Name):
                    if isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Name) and s.value.func.id == "list" and len(s.value.args) == 1:
                        local_list_copies[tgt.id] = mk_compiler().compile(s.value.args[0])
                        locals_env[tgt.id] = local_list_copies[tgt.id]
                    else:
                        locals_env[tgt.id] = mk_compiler().compile(s.value)
                elif isinstance(tgt, ast.Subscript) and isinstance(tgt.value, ast.Name) and tgt.value.id in local_list_copies:
                    idx = mk_compiler().compile(tgt.slice)
                    val = mk_compiler().compile(s.value)
                    cur = local_list_copies[tgt.value.id]
                    updated = f"[{cur} EXCEPT ![({idx}) + 1] = {val}]"
                    local_list_copies[tgt.value.id] = updated
                    locals_env[tgt.value.id] = updated
                else:
                    raise TemporalCompileError(f"Unsupported assignment in {fn.name}: {ast.dump(s)}")
            elif isinstance(s, ast.AugAssign):
                if isinstance(s.target, ast.Attribute) and isinstance(s.target.value, ast.Name) and s.target.value.id == receiver:
                    cur_node = ast.Attribute(value=ast.Name(id=receiver, ctx=ast.Load()), attr=s.target.attr, ctx=ast.Load())
                    binop = ast.BinOp(left=cur_node, op=s.op, right=s.value)
                    state_exprs[s.target.attr] = mk_compiler().compile(binop)
                else:
                    raise TemporalCompileError(f"Unsupported augmented assignment in {fn.name}")
            elif isinstance(s, ast.If):
                cond = mk_compiler().compile(s.test)
                saved_state = dict(state_exprs)
                saved_locals = dict(locals_env)
                saved_lists = dict(local_list_copies)
                saved_ret = ret_expr
                run_stmts(s.body)
                then_state, then_ret = dict(state_exprs), ret_expr
                state_exprs.clear()
                state_exprs.update(saved_state)
                locals_env.clear()
                locals_env.update(saved_locals)
                local_list_copies.clear()
                local_list_copies.update(saved_lists)
                ret_expr = saved_ret
                if s.orelse:
                    run_stmts(s.orelse)
                else_state, else_ret = dict(state_exprs), ret_expr
                for k in list(state_exprs):
                    if then_state[k] != else_state[k]:
                        state_exprs[k] = f"(IF {cond} THEN {then_state[k]} ELSE {else_state[k]})"
                if then_ret != else_ret and then_ret is not None and else_ret is not None:
                    ret_expr = f"(IF {cond} THEN {then_ret} ELSE {else_ret})"
            else:
                raise TemporalCompileError(f"Unsupported statement in {fn.name}: {type(s).__name__}")

    run_stmts(fn.body)
    return state_exprs, ret_expr


def _compile_pure_function(
    fn: ast.FunctionDef,
    extractor: _ModuleExtractor,
    var_types: Dict[str, _TypeInfo],
    needs_helpers: Set[str],
    op_name: str,
) -> Tuple[List[str], str]:
    """Compile a pure Python function (supporting straight-line if/return and single while loops) to TLA+."""
    params = [a.arg for a in fn.args.args]
    extra_defs: List[str] = []

    def compile_block(stmts: List[ast.stmt], env: Dict[str, str]) -> str:
        cur_env = dict(env)

        def comp() -> _ExprCompiler:
            return _ExprCompiler(
                extractor, None, var_types, param_map=cur_env, needs_helpers=needs_helpers
            )

        for idx, s in enumerate(stmts):
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and isinstance(s.value.value, str):
                continue
            if isinstance(s, ast.Return):
                if s.value is None:
                    needs_helpers.add("NONE")
                    return "NONE"
                return comp().compile(s.value)
            if isinstance(s, ast.Assign) and len(s.targets) == 1:
                tgt = s.targets[0]
                if isinstance(tgt, ast.Name):
                    cur_env[tgt.id] = comp().compile(s.value)
                elif isinstance(tgt, ast.Tuple) and isinstance(s.value, ast.Tuple):
                    vals = [comp().compile(v) for v in s.value.elts]
                    for t_elt, val in zip(tgt.elts, vals):
                        if isinstance(t_elt, ast.Name):
                            cur_env[t_elt.id] = val
                else:
                    raise TemporalCompileError(f"Unsupported assignment in pure function {fn.name}")
            elif isinstance(s, ast.If):
                cond = comp().compile(s.test)
                then_expr = compile_block(s.body, cur_env)
                else_stmts = s.orelse if s.orelse else stmts[idx + 1:]
                else_expr = compile_block(else_stmts, cur_env)
                return f"(IF {cond} THEN {then_expr} ELSE {else_expr})"
            elif isinstance(s, ast.While):
                # Compile while loop into a tail-recursive TLA+ operator over loop state variables
                loop_vars = sorted(cur_env.keys())
                all_args = params + [v for v in loop_vars if v not in params]
                loop_name = f"_loop_{op_name}"
                init_vals = [cur_env[v] if v in cur_env else v for v in all_args]

                loop_env = {v: v for v in all_args}
                loop_cond = _ExprCompiler(
                    extractor, None, var_types, param_map=loop_env, needs_helpers=needs_helpers
                ).compile(s.test)
                after_expr = compile_block(stmts[idx + 1:], loop_env)

                def compile_loop_body(body_stmts: List[ast.stmt], lenv: Dict[str, str]) -> str:
                    le = dict(lenv)

                    def lc() -> _ExprCompiler:
                        return _ExprCompiler(
                            extractor, None, var_types, param_map=le, needs_helpers=needs_helpers
                        )

                    for bi, bs in enumerate(body_stmts):
                        if isinstance(bs, ast.Return):
                            if bs.value is None:
                                needs_helpers.add("NONE")
                                return "NONE"
                            return lc().compile(bs.value)
                        if isinstance(bs, ast.Assign) and len(bs.targets) == 1 and isinstance(bs.targets[0], ast.Name):
                            le[bs.targets[0].id] = lc().compile(bs.value)
                        elif isinstance(bs, ast.AugAssign) and isinstance(bs.target, ast.Name):
                            bop = ast.BinOp(left=ast.Name(id=bs.target.id, ctx=ast.Load()), op=bs.op, right=bs.value)
                            le[bs.target.id] = lc().compile(bop)
                        elif isinstance(bs, ast.If):
                            c = lc().compile(bs.test)
                            t_br = compile_loop_body(bs.body, le)
                            e_br = compile_loop_body(bs.orelse if bs.orelse else body_stmts[bi + 1:], le)
                            return f"(IF {c} THEN {t_br} ELSE {e_br})"
                        else:
                            raise TemporalCompileError(f"Unsupported statement in while loop of {fn.name}")
                    next_args = ", ".join(le[v] for v in all_args)
                    return f"{loop_name}({next_args})"

                step_expr = compile_loop_body(s.body, loop_env)
                underscores = ", ".join("_" for _ in all_args)
                extra_defs.append(f"RECURSIVE {loop_name}({underscores})")
                extra_defs.append(
                    f"{loop_name}({', '.join(all_args)}) ==\n"
                    f"  IF {loop_cond} THEN {step_expr}\n"
                    f"  ELSE {after_expr}"
                )
                return f"{loop_name}({', '.join(init_vals)})"
            else:
                raise TemporalCompileError(f"Unsupported statement in pure function {fn.name}: {type(s).__name__}")
        needs_helpers.add("NONE")
        return "NONE"

    body_expr = compile_block(fn.body, {p: p for p in params})
    return extra_defs, body_expr


# ---------------------------------------------------------------------------
# TLA+ & CFG Code Generation
# ---------------------------------------------------------------------------


def _format_cfg_value(val: Any) -> str:
    if isinstance(val, bool):
        return "TRUE" if val else "FALSE"
    if isinstance(val, int):
        return str(val)
    if isinstance(val, str):
        return _tla_string(val)
    if isinstance(val, _ModelValueRef):
        return val.name
    if isinstance(val, _SymmetryVal):
        return "{" + ", ".join(_format_cfg_value(x) for x in val.items) + "}"
    if isinstance(val, (frozenset, set)):
        return "{" + ", ".join(_format_cfg_value(x) for x in val) + "}"
    if isinstance(val, (tuple, list)):
        return "<<" + ", ".join(_format_cfg_value(x) for x in val) + ">>"
    raise TemporalCompileError(f"Unsupported constant value for .cfg: {val!r}")


def _format_domain_tla(val: Any) -> str:
    if isinstance(val, _DomainVal):
        if val.kind == "range":
            return f"({val.start}..{val.stop})"
        if val.kind == "boolean":
            return "BOOLEAN"
        return "{" + ", ".join(_format_cfg_value(x) for x in val.items) + "}"
    if isinstance(val, _SymmetryVal):
        return "{" + ", ".join(_format_cfg_value(x) for x in val.items) + "}"
    if isinstance(val, (frozenset, set, tuple, list)):
        return "{" + ", ".join(_format_cfg_value(x) for x in val) + "}"
    raise TemporalCompileError(f"Unsupported domain value: {val!r}")


def _collect_model_values(obj: Any, out: Set[str]) -> None:
    if isinstance(obj, _ModelValueRef):
        out.add(obj.name)
    elif isinstance(obj, _SymmetryVal):
        for x in obj.items:
            _collect_model_values(x, out)
    elif isinstance(obj, _DomainVal):
        for x in obj.items:
            _collect_model_values(x, out)
    elif isinstance(obj, (tuple, list, set, frozenset)):
        for x in obj:
            _collect_model_values(x, out)
    elif isinstance(obj, dict):
        for k, v in obj.items():
            _collect_model_values(k, out)
            _collect_model_values(v, out)


def _compile_lambda(
    pred: ast.expr,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: Dict[str, _TypeInfo],
    needs_helpers: Set[str],
    *,
    post_by_default: bool = False,
    param_map: Optional[Dict[str, str]] = None,
    state_subst: Optional[Dict[str, str]] = None,
    action_prefix: str = "",
) -> str:
    if isinstance(pred, ast.Lambda):
        receiver = pred.args.args[0].arg if pred.args.args else "self"
        compiler = _ExprCompiler(
            extractor,
            spec,
            var_types,
            receiver=receiver,
            post_by_default=post_by_default,
            param_map=param_map,
            state_subst=state_subst,
            action_prefix=action_prefix,
            needs_helpers=needs_helpers,
        )
        return compiler.compile(pred.body)
    raise TemporalCompileError(f"Expected lambda predicate, got {type(pred).__name__}")


def _compile_func_predicate(
    fn: ast.FunctionDef,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: Dict[str, _TypeInfo],
    needs_helpers: Set[str],
) -> str:
    receiver = fn.args.args[0].arg if fn.args.args else "self"
    lets: List[Tuple[str, str]] = []
    ret_expr: Optional[str] = None
    compiler = _ExprCompiler(extractor, spec, var_types, receiver=receiver, needs_helpers=needs_helpers)
    for stmt in fn.body:
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str):
            continue
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
            lets.append((stmt.targets[0].id, compiler.compile(stmt.value)))
        elif isinstance(stmt, ast.Return) and stmt.value is not None:
            ret_expr = compiler.compile(stmt.value)
        else:
            raise TemporalCompileError(f"Unsupported statement in declarative predicate {fn.name}")
    if ret_expr is None:
        raise TemporalCompileError(f"Declarative predicate {fn.name} has no return statement")
    if lets:
        defs = "\n    ".join(f"{k} == {v}" for k, v in lets)
        return f"(LET {defs} IN {ret_expr})"
    return ret_expr


def _resolve_param_domain(
    model: _ModelDecl,
    spec: _SpecDecl,
    action_name: str,
    param_name: str,
    pinfo: _TypeInfo,
) -> str:
    for key in (f"{action_name}.{param_name}", param_name, pinfo.name or ""):
        if key and key in model.domains:
            # If the domain equals one of the spec's constant values, reference that constant directly
            # so TLC symmetry reduction applies cleanly.
            dom_val = model.domains[key]
            for cname, cval in model.constants.items():
                if cname in spec.constants and cval == dom_val:
                    return cname
            return _format_domain_tla(dom_val)
    if pinfo.literals is not None:
        return "{" + ", ".join(_format_cfg_value(v) for v in pinfo.literals) + "}"
    if pinfo.kind == "bool":
        return "BOOLEAN"
    raise TemporalCompileError(
        f"No finite domain configured for parameter {action_name}.{param_name} "
        f"(type {pinfo.name or pinfo.kind!r}) in model {model.name!r}"
    )


def _compile_spec_model(
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    model: _ModelDecl,
    *,
    mode: str = "all",
    source_path: Optional[str] = None,
) -> CompiledModel:
    mod_name = _sanitize_ident(f"{spec.name}_{model.name}" if model.name != spec.name else spec.name)
    needs_helpers: Set[str] = {"Integers"}
    all_vars = list(spec.states.keys()) + list(spec.ghosts.keys())
    var_types: Dict[str, _TypeInfo] = {}
    for d in (*spec.constants.values(), *spec.states.values(), *spec.ghosts.values()):
        var_types[d.name] = d.type_info
    for p in spec.pure_ops.values():
        var_types[p.name] = p.return_type

    lines: List[str] = []
    cfg_lines: List[str] = []
    cfg_constants: List[str] = []

    # Collect model values from constants and domains
    model_values: Set[str] = set()
    _collect_model_values(model.constants, model_values)
    _collect_model_values(model.domains, model_values)

    # Constants declaration
    const_names = list(spec.constants.keys())
    sym_sets: List[Tuple[str, _SymmetryVal]] = []
    seen_sym: List[_SymmetryVal] = []

    for cname in const_names:
        if cname in model.constants:
            cval = model.constants[cname]
            cfg_constants.append(f"  {cname} = {_format_cfg_value(cval)}")
            if isinstance(cval, _SymmetryVal) and cval not in seen_sym:
                seen_sym.append(cval)
                sym_sets.append((cname, cval))
        elif spec.constants[cname].default is not None:
            cval = extractor._eval_const(spec.constants[cname].default)
            cfg_constants.append(f"  {cname} = {_format_cfg_value(cval)}")

    for dkey, dval in model.domains.items():
        if isinstance(dval, _SymmetryVal) and dval not in seen_sym:
            seen_sym.append(dval)
            sym_cname = _sanitize_ident(f"_SYM_{dkey}")
            const_names.append(sym_cname)
            cfg_constants.append(f"  {sym_cname} = {_format_cfg_value(dval)}")
            sym_sets.append((sym_cname, dval))
            # Update domain lookup to point to the constant name
            model = _ModelDecl(
                **{**model.__dict__, "constants": {**model.constants, sym_cname: dval}}
            )

    for s in model.symmetry:
        if s not in seen_sym:
            seen_sym.append(s)
            sym_cname = f"_SYM_{len(sym_sets)}"
            const_names.append(sym_cname)
            cfg_constants.append(f"  {sym_cname} = {_format_cfg_value(s)}")
            sym_sets.append((sym_cname, s))

    # Pure helper properties / ops
    body_defs: List[str] = []
    for pname, pdecl in spec.pure_ops.items():
        p_expr = _compile_func_predicate(pdecl.func, extractor, spec, var_types, needs_helpers)
        if pdecl.params:
            pargs = ", ".join(p for p, _ in pdecl.params)
            body_defs.append(f"{pname}({pargs}) == {p_expr}")
        else:
            body_defs.append(f"{pname} == {p_expr}")

    # Assumptions
    assume_exprs: List[str] = []
    for a in spec.assumptions:
        if a.expr is not None:
            assume_exprs.append(_compile_lambda(a.expr, extractor, spec, var_types, needs_helpers))
        elif a.func is not None:
            assume_exprs.append(_compile_func_predicate(a.func, extractor, spec, var_types, needs_helpers))
    for cdecl in spec.constants.values():
        for w in cdecl.type_info.wheres:
            if isinstance(w, ast.Lambda) and len(w.args.args) == 1:
                assume_exprs.append(
                    _ExprCompiler(
                        extractor, spec, var_types, param_map={w.args.args[0].arg: cdecl.name}, needs_helpers=needs_helpers
                    ).compile(w.body)
                )
    for idx, aexpr in enumerate(assume_exprs):
        body_defs.append(f"ASSUME {aexpr}")

    # Init
    init_parts: List[str] = []
    for idecl in spec.inits:
        if model.init_override and idecl.name != model.init_override:
            continue
        if idecl.expr is not None:
            init_parts.append(_compile_lambda(idecl.expr, extractor, spec, var_types, needs_helpers))
        elif idecl.func is not None:
            init_parts.append(_compile_func_predicate(idecl.func, extractor, spec, var_types, needs_helpers))
    if not init_parts:
        for vname in all_vars:
            fdecl = spec.states.get(vname) or spec.ghosts[vname]
            if fdecl.default is not None:
                val = _ExprCompiler(extractor, spec, var_types, needs_helpers=needs_helpers).compile(fdecl.default)
                init_parts.append(f"({vname} = {val})")
    init_body = " /\\ ".join(init_parts) if init_parts else "TRUE"
    body_defs.append(f"Init == {init_body}")

    # Actions
    selected_actions = (
        [a for n, a in spec.actions.items() if n in model.actions_override]
        if model.actions_override is not None
        else list(spec.actions.values())
    )
    next_disjuncts: List[str] = []
    conformance_checks: List[Tuple[str, str]] = []
    fairness_parts: List[str] = []
    has_fairness_or_liveness = bool(spec.fairness or spec.properties)

    for act in selected_actions:
        p_types = dict(var_types)
        for pn, pt in act.params:
            p_types[pn] = pt

        # Guards: parameter Where + Requires
        guards: List[str] = []
        for pn, pt in act.params:
            for w in pt.wheres:
                if isinstance(w, ast.Lambda) and len(w.args.args) == 1:
                    guards.append(
                        _ExprCompiler(
                            extractor, spec, p_types, param_map={w.args.args[0].arg: pn}, needs_helpers=needs_helpers
                        ).compile(w.body)
                    )
        for req in act.requires:
            guards.append(_compile_lambda(req, extractor, spec, p_types, needs_helpers))

        # Determine transition body (spec-only vs imperative/conformance)
        use_impl_body = (
            mode != "spec-only"
            and act.has_body
            and act.func is not None
            and not act.is_bool_action
        )

        trans_parts: List[str] = list(guards)
        if use_impl_body:
            assert act.func is not None
            impl_next, impl_ret = _compile_imperative_body(act.func, extractor, spec, p_types, needs_helpers)
            # State variables come from implementation; ghost variables not mutated by impl may be constrained by Action()
            ghost_constrained: Set[str] = set()
            if act.action_preds:
                # Extract ghost updates from Action(pred) if ghost vars were not assigned in Python body
                for ap in act.action_preds:
                    if isinstance(ap, ast.Lambda):
                        for eq_node in ast.walk(ap.body):
                            if isinstance(eq_node, ast.Compare) and len(eq_node.ops) == 1 and isinstance(eq_node.ops[0], ast.Eq):
                                lhs = eq_node.left
                                if isinstance(lhs, ast.Call) and extractor._temporal_name(lhs.func) == "prime" and len(lhs.args) == 1:
                                    arg = lhs.args[0]
                                    if isinstance(arg, ast.Attribute) and arg.attr in spec.ghosts and impl_next[arg.attr] == arg.attr:
                                        receiver = ap.args.args[0].arg if ap.args.args else "self"
                                        impl_next[arg.attr] = _ExprCompiler(
                                            extractor, spec, p_types, receiver=receiver, needs_helpers=needs_helpers
                                        ).compile(eq_node.comparators[0])
                                        ghost_constrained.add(arg.attr)

            for v in all_vars:
                if impl_next[v] == v:
                    trans_parts.append(f"(UNCHANGED {v})")
                else:
                    trans_parts.append(f"({v}' = {impl_next[v]})")

            # Conformance obligations: verify impl transition satisfies Action/Ensures/Preserves/return Where
            if act.action_preds or act.ensures or act.preserves or act.return_type.wheres:
                post_subst = dict(impl_next)
                ob_parts: List[str] = []
                for ap in act.action_preds:
                    # Evaluate Action(pred) with prime(x) -> impl_next[x]
                    ob_parts.append(_compile_conformance_action(ap, extractor, spec, p_types, impl_next, needs_helpers))
                for ens in act.ensures:
                    pmap = {"result": impl_ret} if impl_ret is not None else {}
                    ob_parts.append(
                        _compile_lambda(
                            ens, extractor, spec, p_types, needs_helpers,
                            post_by_default=False, param_map=pmap, state_subst=post_subst
                        )
                        if not _uses_old(ens, extractor)
                        else _compile_conformance_ensures(ens, extractor, spec, p_types, impl_next, impl_ret, needs_helpers)
                    )
                for pres in act.preserves:
                    pre_p = _compile_lambda(pres, extractor, spec, p_types, needs_helpers)
                    post_p = _compile_lambda(pres, extractor, spec, p_types, needs_helpers, state_subst=post_subst)
                    ob_parts.append(f"({pre_p} => {post_p})")
                if impl_ret is not None:
                    for w in act.return_type.wheres:
                        if isinstance(w, ast.Lambda) and len(w.args.args) == 1:
                            ob_parts.append(
                                _ExprCompiler(
                                    extractor, spec, p_types, param_map={w.args.args[0].arg: impl_ret}, needs_helpers=needs_helpers
                                ).compile(w.body)
                            )
                if ob_parts:
                    guard_str = " /\\ ".join(guards) if guards else "TRUE"
                    ob_expr = f"({guard_str} => (" + " /\\ ".join(ob_parts) + "))"
                    for pn, pt in reversed(act.params):
                        dom = _resolve_param_domain(model, spec, act.name, pn, pt)
                        ob_expr = f"(\\A {pn} \\in {dom} : {ob_expr})"
                    conformance_checks.append((f"_Conform_{act.name}", ob_expr))
        else:
            # Declarative action: Action(pred) or bool method body
            if act.action_preds:
                for ap in act.action_preds:
                    trans_parts.append(_compile_lambda(ap, extractor, spec, p_types, needs_helpers))
            elif act.func is not None and act.has_body:
                trans_parts.append(_compile_func_predicate(act.func, extractor, spec, p_types, needs_helpers))
            # Explicit framing
            unchanged_vars: Set[str] = set()
            if act.modifies:
                allowed = set(all_vars)
                for mset in act.modifies:
                    allowed &= set(mset)
                unchanged_vars |= set(all_vars) - allowed
            for uset in act.unchanged:
                unchanged_vars |= set(uset)
            for uv in sorted(unchanged_vars):
                if uv in all_vars:
                    trans_parts.append(f"(UNCHANGED {uv})")

        act_body = " /\\ ".join(trans_parts) if trans_parts else "TRUE"
        if act.params:
            pargs = ", ".join(p for p, _ in act.params)
            body_defs.append(f"{act.name}({pargs}) == {act_body}")
            quant = f"{act.name}({pargs})"
            for pn, pt in reversed(act.params):
                dom = _resolve_param_domain(model, spec, act.name, pn, pt)
                quant = f"(\\E {pn} \\in {dom} : {quant})"
            next_disjuncts.append(quant)
            for wf in act.weak_fairness:
                sub = _fairness_subscript(wf)
                fairness_parts.append(f"WF_{sub}({quant})")
                has_fairness_or_liveness = True
            for sf in act.strong_fairness:
                sub = _fairness_subscript(sf)
                fairness_parts.append(f"SF_{sub}({quant})")
                has_fairness_or_liveness = True
        else:
            body_defs.append(f"{act.name} == {act_body}")
            next_disjuncts.append(act.name)
            for wf in act.weak_fairness:
                sub = _fairness_subscript(wf)
                fairness_parts.append(f"WF_{sub}({act.name})")
                has_fairness_or_liveness = True
            for sf in act.strong_fairness:
                sub = _fairness_subscript(sf)
                fairness_parts.append(f"SF_{sub}({act.name})")
                has_fairness_or_liveness = True

    next_body = " \\/ ".join(next_disjuncts) if next_disjuncts else "FALSE"
    body_defs.append(f"Next == {next_body}")

    # Vars tuple
    vars_tuple = "<<" + ", ".join(all_vars) + ">>" if all_vars else "<<>>"
    body_defs.append(f"_vars == {vars_tuple}")

    # Fairness declarations
    for fdecl in spec.fairness:
        if fdecl.expr is not None:
            fairness_parts.append(_compile_lambda(fdecl.expr, extractor, spec, var_types, needs_helpers))
        elif fdecl.func is not None:
            fairness_parts.append(_compile_func_predicate(fdecl.func, extractor, spec, var_types, needs_helpers))

    # Invariants
    inv_names: List[str] = []
    for inv in spec.invariants:
        if model.invariants_override is not None and inv.name not in model.invariants_override:
            continue
        inv_expr = (
            _compile_lambda(inv.expr, extractor, spec, var_types, needs_helpers)
            if inv.expr is not None
            else _compile_func_predicate(inv.func, extractor, spec, var_types, needs_helpers)  # type: ignore[arg-type]
        )
        body_defs.append(f"{inv.name} == {inv_expr}")
        inv_names.append(inv.name)

    # Inline Where invariants on State/Ghost fields
    for vname in all_vars:
        fdecl = spec.states.get(vname) or spec.ghosts[vname]
        for idx, w in enumerate(fdecl.type_info.wheres):
            if isinstance(w, ast.Lambda) and len(w.args.args) == 1:
                wname = f"_Type_{vname}_{idx}"
                wexpr = _ExprCompiler(
                    extractor, spec, var_types, param_map={w.args.args[0].arg: vname}, needs_helpers=needs_helpers
                ).compile(w.body)
                body_defs.append(f"{wname} == {wexpr}")
                inv_names.append(wname)

    # Conformance invariants
    for cname, cexpr in conformance_checks:
        body_defs.append(f"{cname} == {cexpr}")
        inv_names.append(cname)

    # Action invariants & Temporal properties
    prop_names: List[str] = []
    for ainv in spec.action_invariants:
        aexpr = (
            _compile_lambda(ainv.expr, extractor, spec, var_types, needs_helpers)
            if ainv.expr is not None
            else _compile_func_predicate(ainv.func, extractor, spec, var_types, needs_helpers)  # type: ignore[arg-type]
        )
        body_defs.append(f"{ainv.name} == [][{aexpr}]__vars")
        prop_names.append(ainv.name)
        has_fairness_or_liveness = True

    for prop in spec.properties:
        if model.properties_override is not None and prop.name not in model.properties_override:
            continue
        pexpr = (
            _compile_lambda(prop.expr, extractor, spec, var_types, needs_helpers)
            if prop.expr is not None
            else _compile_func_predicate(prop.func, extractor, spec, var_types, needs_helpers)  # type: ignore[arg-type]
        )
        body_defs.append(f"{prop.name} == {pexpr}")
        prop_names.append(prop.name)
        has_fairness_or_liveness = True

    # Refinement checking (Refines[AbstractSpec])
    for ref in spec.refinements:
        if ref.target_name not in extractor.specs:
            continue
        abs_spec = extractor.specs[ref.target_name]
        abs_subst: Dict[str, str] = {}
        abs_var_types: Dict[str, _TypeInfo] = {}
        for d in (*abs_spec.constants.values(), *abs_spec.states.values(), *abs_spec.ghosts.values()):
            abs_var_types[d.name] = d.type_info
        for abs_var, map_expr in ref.mapping.items():
            op_name = f"_Ref_{ref.name}_{abs_var}"
            compiled_map = _ExprCompiler(
                extractor, spec, var_types, receiver=ref.receiver, needs_helpers=needs_helpers
            ).compile(map_expr)
            body_defs.append(f"{op_name} == {compiled_map}")
            abs_subst[abs_var] = op_name
        # Abstract invariants must hold on every reachable concrete state
        for abs_inv in abs_spec.invariants:
            if abs_inv.expr is not None:
                a_inv_name = f"_Ref_{ref.name}_{abs_inv.name}"
                a_inv_expr = _compile_lambda(
                    abs_inv.expr, extractor, abs_spec, abs_var_types, needs_helpers, state_subst=abs_subst
                )
                body_defs.append(f"{a_inv_name} == {a_inv_expr}")
                inv_names.append(a_inv_name)
        # Abstract temporal properties must hold
        for abs_prop in abs_spec.properties:
            if abs_prop.expr is not None:
                a_prop_name = f"_Ref_{ref.name}_{abs_prop.name}"
                a_prop_expr = _compile_lambda(
                    abs_prop.expr, extractor, abs_spec, abs_var_types, needs_helpers, state_subst=abs_subst
                )
                body_defs.append(f"{a_prop_name} == {a_prop_expr}")
                prop_names.append(a_prop_name)
                has_fairness_or_liveness = True

    # Constraints, view, alias, postcondition
    if model.state_constraint is not None:
        sc = _compile_lambda(model.state_constraint, extractor, spec, var_types, needs_helpers)
        body_defs.append(f"_Constraint == {sc}")
    if model.action_constraint is not None:
        ac = _compile_lambda(model.action_constraint, extractor, spec, var_types, needs_helpers)
        body_defs.append(f"_ActionConstraint == {ac}")
    if model.view is not None:
        vw = _compile_lambda(model.view, extractor, spec, var_types, needs_helpers)
        body_defs.append(f"_View == {vw}")
    if model.alias is not None:
        al = _compile_lambda(model.alias, extractor, spec, var_types, needs_helpers)
        body_defs.append(f"_Alias == {al}")
    if model.postcondition is not None:
        pc = _compile_lambda(model.postcondition, extractor, spec, var_types, needs_helpers)
        body_defs.append(f"_Postcondition == {pc}")

    # Symmetry definition (TLC/Manyan skips SYMMETRY when checking liveness properties)
    use_symmetry = bool(sym_sets) and not prop_names
    if use_symmetry:
        needs_helpers.add("TLC")
        perms = " \\cup ".join(f"Permutations({cname})" for cname, _ in sym_sets)
        body_defs.append(f"_Symmetry == {perms}")

    # Spec formula
    if has_fairness_or_liveness:
        spec_parts = ["Init", "[][Next]__vars"] + fairness_parts
        body_defs.append("Spec == " + " /\\ ".join(spec_parts))

    # Assemble TLA+ module header
    extends = [m for m in ("Integers", "Sequences", "FiniteSets", "TLC") if m in needs_helpers]
    if "NONE" in needs_helpers:
        model_values.add("NONE")
    for mv in sorted(model_values):
        if mv not in const_names:
            const_names.append(mv)
            cfg_constants.append(f"  {mv} = {mv}")

    lines.append(f"---- MODULE {mod_name} ----")
    if extends:
        lines.append("EXTENDS " + ", ".join(extends))
    if const_names:
        lines.append("CONSTANTS " + ", ".join(const_names))
    if all_vars:
        lines.append("VARIABLES " + ", ".join(all_vars))
    if "_Sum" in needs_helpers:
        lines.append("RECURSIVE _Sum(_)")
        lines.append("_Sum(s) == IF Len(s) = 0 THEN 0 ELSE Head(s) + _Sum(Tail(s))")
    lines.append("")
    lines.extend(body_defs)
    lines.append("====")

    # Assemble .cfg
    if has_fairness_or_liveness:
        cfg_lines.append("SPECIFICATION Spec")
    else:
        cfg_lines.append("INIT Init")
        cfg_lines.append("NEXT Next")
    if cfg_constants:
        cfg_lines.append("CONSTANTS")
        cfg_lines.extend(cfg_constants)
    for inv_name in inv_names:
        cfg_lines.append(f"INVARIANT {inv_name}")
    for prop_name in prop_names:
        cfg_lines.append(f"PROPERTY {prop_name}")
    if model.state_constraint is not None:
        cfg_lines.append("CONSTRAINT _Constraint")
    if model.action_constraint is not None:
        cfg_lines.append("ACTION_CONSTRAINT _ActionConstraint")
    if use_symmetry:
        cfg_lines.append("SYMMETRY _Symmetry")
    if model.view is not None:
        cfg_lines.append("VIEW _View")
    if model.alias is not None:
        cfg_lines.append("ALIAS _Alias")
    if model.postcondition is not None:
        cfg_lines.append("POSTCONDITION _Postcondition")
    if not model.check_deadlock:
        cfg_lines.append("CHECK_DEADLOCK FALSE")

    return CompiledModel(
        name=model.name,
        module_name=mod_name,
        tla="\n".join(lines) + "\n",
        cfg="\n".join(cfg_lines) + "\n",
        source=source_path,
        spec_name=spec.name,
        model_name=model.name,
    )


def _fairness_subscript(vars_tuple: Tuple[str, ...]) -> str:
    if not vars_tuple:
        return "_vars"
    if len(vars_tuple) == 1:
        return vars_tuple[0]
    return "<<" + ", ".join(vars_tuple) + ">>"


def _uses_old(expr: ast.expr, extractor: _ModuleExtractor) -> bool:
    return any(
        isinstance(n, ast.Call) and extractor._temporal_name(n.func) == "old"
        for n in ast.walk(expr)
    )


def _compile_conformance_action(
    pred: ast.expr,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: Dict[str, _TypeInfo],
    impl_next: Dict[str, str],
    needs_helpers: Set[str],
) -> str:
    """Evaluate Action(pred) substituting prime(s.v) -> impl_next[v] and s.v -> v."""
    assert isinstance(pred, ast.Lambda)
    receiver = pred.args.args[0].arg if pred.args.args else "self"

    class _SubstCompiler(_ExprCompiler):
        def _state_ref(self, attr: str, primed: bool) -> str:
            if primed and attr in impl_next:
                return f"({impl_next[attr]})"
            return super()._state_ref(attr, primed=False)

    return _SubstCompiler(
        extractor, spec, var_types, receiver=receiver, needs_helpers=needs_helpers
    ).compile(pred.body)


def _compile_conformance_ensures(
    pred: ast.expr,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: Dict[str, _TypeInfo],
    impl_next: Dict[str, str],
    impl_ret: Optional[str],
    needs_helpers: Set[str],
) -> str:
    """Evaluate Ensures(pred) with old(s.v) -> v, bare s.v -> impl_next[v], result -> impl_ret."""
    assert isinstance(pred, ast.Lambda)
    receiver = pred.args.args[0].arg if pred.args.args else "self"
    pmap = {"result": impl_ret} if impl_ret is not None else {}

    class _EnsCompiler(_ExprCompiler):
        def _state_ref(self, attr: str, primed: bool) -> str:
            if primed and attr in impl_next:
                return f"({impl_next[attr]})"
            return super()._state_ref(attr, primed=False)

    return _EnsCompiler(
        extractor, spec, var_types, receiver=receiver, post_by_default=True, param_map=pmap, needs_helpers=needs_helpers
    ).compile(pred.body)


def _compile_standalone_function_model(
    extractor: _ModuleExtractor,
    fn: _PureDecl,
    *,
    source_path: Optional[str] = None,
) -> CompiledModel:
    mod_name = _sanitize_ident(f"Fn_{fn.name}")
    needs_helpers: Set[str] = {"Integers"}
    var_types = {p: pt for p, pt in fn.params}
    extra_defs, body_expr = _compile_pure_function(fn.func, extractor, var_types, needs_helpers, fn.name)

    pargs = ", ".join(p for p, _ in fn.params)
    call_expr = f"{fn.name}({pargs})" if pargs else fn.name

    # Build small bounded default domains for standalone pure function verification
    def default_domain(pt: _TypeInfo) -> str:
        if pt.kind == "int":
            return "(0..6)" if pt.wheres else "(-3..3)"
        if pt.kind == "bool":
            return "BOOLEAN"
        if pt.kind == "seq":
            needs_helpers.add("Sequences")
            return "{<<>>, <<1>>, <<1, 3>>, <<1, 3, 5>>, <<2, 2, 4>>}"
        return "{0, 1, 2}"

    arg_map = {p: f"_arg_{p}" for p, _ in fn.params}
    pre_parts: List[str] = []
    for pn, pt in fn.params:
        for w in pt.wheres:
            if isinstance(w, ast.Lambda) and len(w.args.args) == 1:
                pre_parts.append(
                    _ExprCompiler(
                        extractor, None, var_types, param_map={w.args.args[0].arg: arg_map[pn]}, needs_helpers=needs_helpers
                    ).compile(w.body)
                )
    for req in fn.requires:
        if isinstance(req, ast.Lambda):
            pre_parts.append(
                _ExprCompiler(extractor, None, var_types, param_map=arg_map, needs_helpers=needs_helpers).compile(req.body)
            )

    post_parts: List[str] = []
    for w in fn.return_type.wheres:
        if isinstance(w, ast.Lambda) and len(w.args.args) == 1:
            w_expr = _ExprCompiler(
                extractor, None, var_types, param_map={w.args.args[0].arg: "result"}, needs_helpers=needs_helpers
            ).compile(w.body)
            if fn.return_type.nullable:
                needs_helpers.add("NONE")
                w_expr = f"((result # NONE) => {w_expr})"
            post_parts.append(w_expr)
    for ens in fn.ensures:
        if isinstance(ens, ast.Lambda):
            post_parts.append(
                _ExprCompiler(extractor, None, var_types, param_map=arg_map, needs_helpers=needs_helpers).compile(ens.body)
            )

    pre_str = " /\\ ".join(pre_parts) if pre_parts else "TRUE"
    post_str = " /\\ ".join(post_parts) if post_parts else "TRUE"

    extends = [m for m in ("Integers", "Sequences", "FiniteSets") if m in needs_helpers]
    lines = [f"---- MODULE {mod_name} ----", "EXTENDS " + ", ".join(extends)]
    if "NONE" in needs_helpers:
        lines.append("CONSTANTS NONE")

    if fn.params:
        state_vars = [arg_map[p] for p, _ in fn.params]
        lines.append("VARIABLES " + ", ".join(state_vars))
        lines.extend(extra_defs)
        lines.append(f"{fn.name}({pargs}) == {body_expr}")
        arg_call = f"{fn.name}(" + ", ".join(state_vars) + ")"
        dom_parts = [f"({arg_map[pn]} \\in {default_domain(pt)})" for pn, pt in fn.params] + pre_parts
        lines.append("Init == " + " /\\ ".join(dom_parts))
        unchanged_str = state_vars[0] if len(state_vars) == 1 else "<<" + ", ".join(state_vars) + ">>"
        lines.append(f"Next == UNCHANGED {unchanged_str}")
        lines.append(f"Contract_{fn.name} == (LET result == {arg_call} IN {post_str})")
    else:
        lines.append("VARIABLES _done")
        lines.extend(extra_defs)
        lines.append(f"{fn.name} == {body_expr}")
        lines.append("Init == _done = TRUE")
        lines.append("Next == UNCHANGED _done")
        lines.append(f"Contract_{fn.name} == (_done => ({pre_str} => (LET result == {call_expr} IN {post_str})))")

    lines.append("====")

    cfg_lines = ["INIT Init", "NEXT Next"]
    if "NONE" in needs_helpers:
        cfg_lines.append("CONSTANT NONE = NONE")
    cfg_lines.append(f"INVARIANT Contract_{fn.name}")

    return CompiledModel(
        name=fn.name,
        module_name=mod_name,
        tla="\n".join(lines) + "\n",
        cfg="\n".join(cfg_lines) + "\n",
        source=source_path,
        spec_name=fn.name,
        model_name=None,
    )


# ---------------------------------------------------------------------------
# Public Compiler Entry Points
# ---------------------------------------------------------------------------


def compile_source(
    source: str,
    *,
    source_path: Optional[str] = None,
    spec: Optional[str] = None,
    model: Optional[str] = None,
    mode: str = "all",
) -> List[CompiledModel]:
    """Compile Temporal declarations in Python source text to TLA+ models."""
    tree = ast.parse(source, filename=source_path or "<temporal>")
    extractor = _ModuleExtractor(tree, source_path=source_path)
    extractor.extract()

    compiled: List[CompiledModel] = []

    if extractor.models:
        for m in extractor.models:
            if model is not None and m.name != model:
                continue
            if spec is not None and m.spec_name != spec:
                continue
            if m.spec_name not in extractor.specs:
                raise TemporalCompileError(
                    f"Model {m.name!r} references unknown specification {m.spec_name!r}"
                )
            compiled.append(
                _compile_spec_model(
                    extractor, extractor.specs[m.spec_name], m, mode=mode, source_path=source_path
                )
            )
    elif extractor.specs:
        for sname, sdecl in extractor.specs.items():
            if spec is not None and sname != spec:
                continue
            if sdecl.is_protocol and any(not other.is_protocol for other in extractor.specs.values()):
                continue
            default_model = _ModelDecl(name=sname, spec_name=sname)
            compiled.append(
                _compile_spec_model(
                    extractor, sdecl, default_model, mode=mode, source_path=source_path
                )
            )

    if model is None:
        for fn in extractor.functions:
            if spec is not None and fn.name != spec:
                continue
            compiled.append(
                _compile_standalone_function_model(extractor, fn, source_path=source_path)
            )

    return compiled


def compile_file(
    path: Union[str, Path],
    *,
    spec: Optional[str] = None,
    model: Optional[str] = None,
    mode: str = "all",
) -> List[CompiledModel]:
    """Read a Python file and compile all Temporal models/contracts in it."""
    p = Path(path)
    return compile_source(
        p.read_text(encoding="utf-8"),
        source_path=str(p),
        spec=spec,
        model=model,
        mode=mode,
    )
