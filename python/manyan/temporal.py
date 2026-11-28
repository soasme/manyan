"""Compile Python source annotated with `temporal` into TLA+ models for Manyan.

This module analyses Python source purely via `ast` without importing or
executing user code. It extracts Temporal declarations (`State`, `Constant`,
`Ghost`, `Pure`, `Assume`, `Init`, `Action`, `Invariant`, `ActionInvariant`,
`Property`, `Fairness`, `Where`, `Requires`, `Ensures`, `Preserves`,
`Modifies`, `Unchanged`, `WeakFairness`, `StrongFairness`, `Refines`,
`ModelValue`, `Symmetry`, `Domain`, `Model`), compiles them into TLA+ modules
and `.cfg` configurations, and hands them to Manyan for model checking.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional, Union


class TemporalCompileError(ValueError):
    """Raised when a Temporal declaration cannot be translated to TLA+."""


# ---------------------------------------------------------------------------
# Internal IR
# ---------------------------------------------------------------------------

_CLAUSE_FIELDS: dict[str, tuple[str, str]] = {
    "Assume": ("assume", "assumptions"),
    "Init": ("init", "inits"),
    "Invariant": ("invariant", "invariants"),
    "ActionInvariant": ("action_invariant", "action_invariants"),
    "Property": ("property", "properties"),
    "Fairness": ("fairness", "fairness"),
}

_ACTION_CLAUSES = frozenset({
    "Action",
    "Requires",
    "Ensures",
    "Preserves",
    "Modifies",
    "Unchanged",
    "WeakFairness",
    "StrongFairness",
})


@dataclass
class _TypeInfo:
    kind: str  # "int", "bool", "str", "seq", "set", "map", "model", "none", "any"
    elem: Optional[_TypeInfo] = None
    key: Optional[_TypeInfo] = None
    val: Optional[_TypeInfo] = None
    name: Optional[str] = None
    literals: Optional[tuple[Any, ...]] = None
    wheres: list[ast.expr] = field(default_factory=list)
    nullable: bool = False

    def with_nullable(self) -> _TypeInfo:
        return _TypeInfo(
            self.kind, self.elem, self.key, self.val, self.name,
            self.literals, list(self.wheres), nullable=True,
        )

    def with_wheres(self, extra: list[ast.expr]) -> _TypeInfo:
        return _TypeInfo(
            self.kind, self.elem, self.key, self.val, self.name,
            self.literals, list(self.wheres) + extra, nullable=self.nullable,
        )


@dataclass
class _FieldDecl:
    name: str
    role: str  # "constant", "state", "ghost"
    type_info: _TypeInfo
    default: Optional[ast.expr] = None


@dataclass
class _ClauseDecl:
    name: str
    kind: str
    expr: Optional[ast.expr] = None
    func: Optional[ast.FunctionDef] = None


@dataclass
class _ActionDecl:
    name: str
    params: list[tuple[str, _TypeInfo]] = field(default_factory=list)
    return_type: _TypeInfo = field(default_factory=lambda: _TypeInfo("any"))
    requires: list[ast.expr] = field(default_factory=list)
    ensures: list[ast.expr] = field(default_factory=list)
    preserves: list[ast.expr] = field(default_factory=list)
    action_preds: list[ast.expr] = field(default_factory=list)
    modifies: list[tuple[str, ...]] = field(default_factory=list)
    unchanged: list[tuple[str, ...]] = field(default_factory=list)
    weak_fairness: list[tuple[str, ...]] = field(default_factory=list)
    strong_fairness: list[tuple[str, ...]] = field(default_factory=list)
    func: Optional[ast.FunctionDef] = None
    has_body: bool = False
    is_bool_action: bool = False


@dataclass
class _PureDecl:
    name: str
    params: list[tuple[str, _TypeInfo]]
    return_type: _TypeInfo
    func: ast.FunctionDef
    is_property: bool = False
    requires: list[ast.expr] = field(default_factory=list)
    ensures: list[ast.expr] = field(default_factory=list)


@dataclass
class _RefineDecl:
    name: str
    target_name: str
    mapping: dict[str, ast.expr]
    receiver: str


@dataclass
class _SpecDecl:
    name: str
    bases: list[str] = field(default_factory=list)
    type_params: list[str] = field(default_factory=list)
    is_protocol: bool = False
    is_module: bool = False
    constants: dict[str, _FieldDecl] = field(default_factory=dict)
    states: dict[str, _FieldDecl] = field(default_factory=dict)
    ghosts: dict[str, _FieldDecl] = field(default_factory=dict)
    assumptions: list[_ClauseDecl] = field(default_factory=list)
    inits: list[_ClauseDecl] = field(default_factory=list)
    invariants: list[_ClauseDecl] = field(default_factory=list)
    action_invariants: list[_ClauseDecl] = field(default_factory=list)
    properties: list[_ClauseDecl] = field(default_factory=list)
    fairness: list[_ClauseDecl] = field(default_factory=list)
    actions: dict[str, _ActionDecl] = field(default_factory=dict)
    pure_ops: dict[str, _PureDecl] = field(default_factory=dict)
    refinements: list[_RefineDecl] = field(default_factory=list)

    def add_clause(
        self,
        cname: str,
        name: str,
        expr: Optional[ast.expr] = None,
        func: Optional[ast.FunctionDef] = None,
    ) -> None:
        kind, attr = _CLAUSE_FIELDS[cname]
        getattr(self, attr).append(_ClauseDecl(name=name, kind=kind, expr=expr, func=func))

    def add_field(self, decl: _FieldDecl) -> None:
        attr = {"constant": "constants", "state": "states", "ghost": "ghosts"}[decl.role]
        getattr(self, attr)[decl.name] = decl


@dataclass(frozen=True)
class _ModelValueRef:
    sort: str
    name: str


@dataclass(frozen=True)
class _SymmetryVal:
    items: tuple[Any, ...]


@dataclass(frozen=True)
class _DomainVal:
    kind: str  # "range", "values", "boolean"
    start: int = 0
    stop: int = 0
    items: tuple[Any, ...] = ()


@dataclass
class _ModelDecl:
    name: str
    spec_name: str
    constants: dict[str, Any] = field(default_factory=dict)
    domains: dict[str, Any] = field(default_factory=dict)
    init_override: Optional[str] = None
    actions_override: Optional[list[str]] = None
    invariants_override: Optional[list[str]] = None
    properties_override: Optional[list[str]] = None
    state_constraint: Optional[ast.expr] = None
    action_constraint: Optional[ast.expr] = None
    symmetry: list[_SymmetryVal] = field(default_factory=list)
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


def _is_ellipsis_body(body: list[ast.stmt]) -> bool:
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
    return ("M_" + clean) if (not clean or clean[0].isdigit()) else clean


def _tla_string(s: str) -> str:
    esc = (
        s.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\t", "\\t")
        .replace("\r", "\\r")
    )
    return f'"{esc}"'


def _neg_int_const(node: ast.expr) -> Optional[int]:
    if (
        isinstance(node, ast.UnaryOp)
        and isinstance(node.op, ast.USub)
        and isinstance(node.operand, ast.Constant)
        and isinstance(node.operand.value, int)
        and not isinstance(node.operand.value, bool)
    ):
        return node.operand.value
    return None


# ---------------------------------------------------------------------------
# Module Extractor
# ---------------------------------------------------------------------------


class _ModuleExtractor:
    def __init__(self, tree: ast.Module, source_path: Optional[str] = None) -> None:
        self.tree = tree
        self.source_path = source_path
        self.module_spec_name = _sanitize_ident(Path(source_path).stem) if source_path else "Module"
        self.temporal_aliases: dict[str, str] = {}
        self.temporal_modules: set[str] = set()
        self.model_value_sorts: set[str] = {"ModelValue"}
        self.type_aliases: dict[str, _TypeInfo] = {}
        self.typevars: set[str] = set()
        self.env: dict[str, Any] = {}
        self.specs: dict[str, _SpecDecl] = {}
        self.models: list[_ModelDecl] = []
        self.functions: dict[str, _PureDecl] = {}

    def _temporal_name(self, node: ast.expr) -> Optional[str]:
        if isinstance(node, ast.Name):
            return self.temporal_aliases.get(node.id)
        if (
            isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id in self.temporal_modules
        ):
            return node.attr
        return None

    def _is_annotated(self, node: ast.expr) -> bool:
        return isinstance(node, ast.Subscript) and _dotted_name(node.value) in ("Annotated", "typing.Annotated")

    def _unwrap_classvar(self, node: ast.expr) -> ast.expr:
        while isinstance(node, ast.Subscript) and _dotted_name(node.value) in ("ClassVar", "typing.ClassVar"):
            node = node.slice
        return node

    def _annotated_parts(self, node: ast.expr) -> tuple[ast.expr, list[ast.expr]]:
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
        base, meta = self._annotated_parts(node)
        wheres = [
            m.args[0]
            for m in meta
            if isinstance(m, ast.Call) and self._temporal_name(m.func) == "Where" and m.args
        ]
        info = self._resolve_bare_type(base)
        return info.with_wheres(wheres) if wheres else info

    def _resolve_bare_type(self, node: ast.expr) -> _TypeInfo:
        if isinstance(node, ast.Subscript):
            tname = self._temporal_name(node.value)
            if tname in ("State", "Constant", "Ghost", "Pure"):
                return self._resolve_type(node.slice)
            head = _dotted_name(node.value) or ""
            if head in ("Optional", "typing.Optional"):
                return self._resolve_type(node.slice).with_nullable()
            if head in ("Union", "typing.Union") and isinstance(node.slice, ast.Tuple):
                non_none = [e for e in node.slice.elts if not (isinstance(e, ast.Constant) and e.value is None)]
                has_none = len(non_none) < len(node.slice.elts)
                if len(non_none) == 1:
                    inner = self._resolve_type(non_none[0])
                    return inner.with_nullable() if has_none else inner
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
            if isinstance(node.left, ast.Constant) and node.left.value is None:
                return self._resolve_type(node.right).with_nullable()
            if isinstance(node.right, ast.Constant) and node.right.value is None:
                return self._resolve_type(node.left).with_nullable()
            return _TypeInfo("any")
        if isinstance(node, ast.Name):
            if node.id in self.type_aliases:
                return self.type_aliases[node.id]
            if node.id in ("int", "bool", "str"):
                return _TypeInfo(node.id, name=node.id)
            if node.id in self.model_value_sorts:
                return _TypeInfo("model", name=node.id)
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
            return {
                self._eval_const(k): self._eval_const(v)
                for k, v in zip(node.keys, node.values)
                if k is not None
            }
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
                return _SymmetryVal(tuple(self._eval_const(node.args[0]))) if node.args else _SymmetryVal(())
            if isinstance(node.func, ast.Name) and node.func.id in self.model_value_sorts and len(node.args) == 1:
                return _ModelValueRef(node.func.id, str(self._eval_const(node.args[0])))
            if isinstance(node.func, ast.Name) and node.func.id == "frozenset":
                return frozenset(self._eval_const(node.args[0])) if node.args else frozenset()
            if isinstance(node.func, ast.Name) and node.func.id == "range":
                r = range(*(int(self._eval_const(a)) for a in node.args))
                return _DomainVal("range", r.start, r.stop - 1) if r.step == 1 else _DomainVal("values", items=tuple(r))
            if isinstance(node.func, ast.Attribute) and self._temporal_name(node.func.value) == "Domain":
                if node.func.attr == "range" and len(node.args) == 2:
                    return _DomainVal("range", int(self._eval_const(node.args[0])), int(self._eval_const(node.args[1])))
                if node.func.attr == "values":
                    return _DomainVal("values", items=tuple(self._eval_const(a) for a in node.args))
                if node.func.attr == "boolean":
                    return _DomainVal("boolean")
        raise TemporalCompileError(f"Unsupported constant expression: {ast.dump(node)}")

    def extract(self) -> None:
        for stmt in self.tree.body:
            if isinstance(stmt, ast.ImportFrom) and stmt.module == "temporal":
                for alias in stmt.names:
                    self.temporal_aliases[alias.asname or alias.name] = alias.name
            elif isinstance(stmt, ast.Import):
                for alias in stmt.names:
                    if alias.name == "temporal":
                        self.temporal_modules.add(alias.asname or alias.name)

        mod_spec = _SpecDecl(name=self.module_spec_name, is_module=True)
        has_mod_spec = False

        for stmt in self.tree.body:
            if isinstance(stmt, ast.ClassDef):
                self._extract_class(stmt)
            elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                if self._extract_attr_into(mod_spec, stmt):
                    has_mod_spec = True
                elif stmt.value is not None:
                    self._extract_assign(stmt.target.id, stmt.value)
            elif isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
                self._extract_assign(stmt.targets[0].id, stmt.value)
            elif isinstance(stmt, ast.FunctionDef):
                if has_mod_spec and self._extract_method_into(mod_spec, stmt, is_method=False):
                    continue
                fn = self._extract_standalone_function(stmt)
                if fn is not None:
                    self.functions[fn.name] = fn
                elif self._extract_method_into(mod_spec, stmt, is_method=False):
                    has_mod_spec = True

        if has_mod_spec:
            self.specs[mod_spec.name] = mod_spec

    def _extract_assign(self, name: str, value: ast.expr) -> None:
        if isinstance(value, ast.Call):
            if _dotted_name(value.func) in ("TypeVar", "typing.TypeVar"):
                self.typevars.add(name)
                return
            if self._temporal_name(value.func) == "Model":
                self.models.append(self._extract_model(name, value))
                return
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

    def _extract_annotated_spec_alias(self, name: str, base_name: str, meta: list[ast.expr]) -> None:
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
                if cname in _CLAUSE_FIELDS:
                    derived.add_clause(cname, f"{_CLAUSE_FIELDS[cname][0]}_{idx}", expr=m.args[0] if m.args else None)
        self.specs[name] = derived

    def _extract_class(self, cls: ast.ClassDef) -> None:
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
                elif isinstance(b.value, ast.Name) and b.value.id in self.specs:
                    spec.bases.append(b.value.id)
                elts = b.slice.elts if isinstance(b.slice, ast.Tuple) else [b.slice]
                for e in elts:
                    if isinstance(e, ast.Name) and e.id in self.typevars and e.id not in spec.type_params:
                        spec.type_params.append(e.id)

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
            if (
                (isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name) and self._extract_attr_into(spec, stmt))
                or (isinstance(stmt, ast.FunctionDef) and self._extract_method_into(spec, stmt, is_method=True))
            ):
                has_temporal = True

        if has_temporal:
            self.specs[cls.name] = spec

    def _extract_attr_into(self, spec: _SpecDecl, stmt: ast.AnnAssign) -> bool:
        assert isinstance(stmt.target, ast.Name)
        name = stmt.target.id
        ann = self._unwrap_classvar(stmt.annotation)

        if isinstance(ann, ast.Subscript):
            tname = self._temporal_name(ann.value)
            if tname in ("Constant", "State", "Ghost"):
                spec.add_field(_FieldDecl(name=name, role=tname.lower(), type_info=self._resolve_type(ann.slice), default=stmt.value))
                return True

        base, meta = self._annotated_parts(ann)
        if not meta:
            return False

        if isinstance(base, ast.Subscript):
            tname = self._temporal_name(base.value)
            if tname in ("Constant", "State", "Ghost"):
                spec.add_field(_FieldDecl(name=name, role=tname.lower(), type_info=self._resolve_type(ann), default=stmt.value))
                return True

        found = False
        action_decl: Optional[_ActionDecl] = None
        for m in meta:
            if not isinstance(m, ast.Call):
                continue
            cname = self._temporal_name(m.func)
            if cname in _CLAUSE_FIELDS:
                spec.add_clause(cname, name, expr=m.args[0] if m.args else None)
                found = True
            elif cname in _ACTION_CLAUSES:
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
        elif cname == "Action" and call.args:
            action.action_preds.append(call.args[0])
        elif cname in ("Modifies", "Unchanged", "WeakFairness", "StrongFairness"):
            vnames = tuple(str(self._eval_const(a)) for a in call.args)
            attr = {
                "Modifies": "modifies",
                "Unchanged": "unchanged",
                "WeakFairness": "weak_fairness",
                "StrongFairness": "strong_fairness",
            }[cname]
            getattr(action, attr).append(vnames)

    def _extract_method_into(self, spec: _SpecDecl, fn: ast.FunctionDef, *, is_method: bool) -> bool:
        if fn.returns is None:
            return False

        is_prop = any(isinstance(d, ast.Name) and d.id == "property" for d in fn.decorator_list)
        ret_base, ret_meta = self._annotated_parts(fn.returns)
        arg_list = fn.args.args[1:] if is_method else fn.args.args

        if isinstance(ret_base, ast.Subscript) and self._temporal_name(ret_base.value) == "Refines":
            target_node = ret_base.slice
            target_name = (
                target_node.value.id
                if isinstance(target_node, ast.Subscript) and isinstance(target_node.value, ast.Name)
                else (target_node.id if isinstance(target_node, ast.Name) else "")
            )
            mapping: dict[str, ast.expr] = {}
            ref_receiver = fn.args.args[0].arg if fn.args.args else "self"
            for stmt in fn.body:
                if isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.Call) and self._temporal_name(stmt.value.func) == "Refines":
                    for kw in stmt.value.keywords:
                        if kw.arg is not None:
                            mapping[kw.arg] = kw.value
            spec.refinements.append(_RefineDecl(name=fn.name, target_name=target_name, mapping=mapping, receiver=ref_receiver))
            return True

        if isinstance(ret_base, ast.Subscript) and self._temporal_name(ret_base.value) == "Pure":
            params = [(a.arg, self._resolve_type(a.annotation)) for a in arg_list]
            spec.pure_ops[fn.name] = _PureDecl(
                name=fn.name, params=params, return_type=self._resolve_type(ret_base.slice), func=fn, is_property=is_prop
            )
            return True

        if not ret_meta:
            return False

        for m in ret_meta:
            if isinstance(m, ast.Call):
                cname = self._temporal_name(m.func)
                if cname in _CLAUSE_FIELDS:
                    spec.add_clause(cname, fn.name, expr=m.args[0] if m.args else None, func=fn)
                    return True

        if not any(isinstance(m, ast.Call) and self._temporal_name(m.func) in _ACTION_CLAUSES for m in ret_meta):
            return False

        params = [(a.arg, self._resolve_type(a.annotation)) for a in arg_list]
        ret_type = self._resolve_type(fn.returns)
        receiver = fn.args.args[0].arg if (is_method and fn.args.args) else None
        mutates_state = any(
            (
                isinstance(s, ast.Assign)
                and any(
                    (receiver is not None and isinstance(t, ast.Attribute) and isinstance(t.value, ast.Name) and t.value.id == receiver)
                    or (receiver is None and isinstance(t, ast.Name) and t.id in spec.states)
                    for t in s.targets
                )
            )
            or (
                isinstance(s, ast.AugAssign)
                and (
                    (receiver is not None and isinstance(s.target, ast.Attribute) and isinstance(s.target.value, ast.Name) and s.target.value.id == receiver)
                    or (receiver is None and isinstance(s.target, ast.Name) and s.target.id in spec.states)
                )
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
                and not any(isinstance(m, ast.Call) and self._temporal_name(m.func) == "Ensures" for m in ret_meta)
            ),
        )
        for m in ret_meta:
            if isinstance(m, ast.Call):
                cname = self._temporal_name(m.func)
                if cname in _ACTION_CLAUSES:
                    self._add_action_clause(action, cname, m)
        spec.actions[fn.name] = action
        return True

    def _extract_standalone_function(self, fn: ast.FunctionDef) -> Optional[_PureDecl]:
        if fn.returns is None:
            return None
        ret_base, ret_meta = self._annotated_parts(fn.returns)
        is_pure = isinstance(ret_base, ast.Subscript) and self._temporal_name(ret_base.value) == "Pure"
        requires = [
            m.args[0] for m in ret_meta
            if isinstance(m, ast.Call) and self._temporal_name(m.func) == "Requires" and m.args
        ]
        ensures = [
            m.args[0] for m in ret_meta
            if isinstance(m, ast.Call) and self._temporal_name(m.func) == "Ensures" and m.args
        ]
        if not (is_pure or requires or ensures):
            return None
        params = [(a.arg, self._resolve_type(a.annotation)) for a in fn.args.args]
        return _PureDecl(
            name=fn.name, params=params, return_type=self._resolve_type(fn.returns),
            func=fn, requires=requires, ensures=ensures,
        )

    def _extract_model(self, name: str, call: ast.Call) -> _ModelDecl:
        if not call.args:
            raise TemporalCompileError(f"Model {name!r} requires a specification argument")
        spec_arg = call.args[0]
        if isinstance(spec_arg, ast.Subscript) and isinstance(spec_arg.value, ast.Name):
            spec_name = spec_arg.value.id
        elif isinstance(spec_arg, ast.Name):
            spec_name = spec_arg.id
        elif isinstance(spec_arg, ast.Subscript) and _dotted_name(spec_arg.value) == "sys.modules":
            spec_name = self.module_spec_name
        else:
            raise TemporalCompileError(f"Unsupported Model spec target in {name!r}")

        model = _ModelDecl(name=name, spec_name=spec_name)
        for kw in call.keywords:
            if kw.arg == "constants":
                val = self._eval_const(kw.value)
                if isinstance(val, dict):
                    model.constants.update(val)
            elif kw.arg == "domains" and isinstance(kw.value, ast.Dict):
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
            elif kw.arg in ("state_constraint", "action_constraint", "view", "alias", "postcondition"):
                setattr(model, kw.arg, kw.value)
            elif kw.arg == "symmetry":
                for item in self._eval_const(kw.value):
                    if isinstance(item, _SymmetryVal):
                        model.symmetry.append(item)
            elif kw.arg in ("actions", "invariants", "properties"):
                items = kw.value.elts if isinstance(kw.value, (ast.Tuple, ast.List)) else []
                names = [
                    e.attr if isinstance(e, ast.Attribute) else (e.id if isinstance(e, ast.Name) else "")
                    for e in items
                ]
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
        var_types: dict[str, _TypeInfo],
        receiver: Optional[str] = None,
        post_by_default: bool = False,
        param_map: Optional[dict[str, str]] = None,
        state_subst: Optional[dict[str, str]] = None,
        action_prefix: str = "",
        needs_helpers: Optional[set[str]] = None,
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

    def _reserved_names(self) -> set[str]:
        reserved = set(self.var_types.keys())
        for m in self.extractor.models:
            _collect_model_values(m.constants, reserved)
            _collect_model_values(m.domains, reserved)
        return reserved

    def _sub(self, *, use_prime: bool, extra_params: dict[str, str]) -> _ExprCompiler:
        return _ExprCompiler(
            self.extractor,
            self.spec,
            self.var_types,
            receiver=self.receiver,
            post_by_default=use_prime,
            param_map={**self.param_map, **extra_params},
            state_subst=self.state_subst,
            action_prefix=self.action_prefix,
            needs_helpers=self.needs_helpers,
        )

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
                if node.func.id in ("frozenset", "set", "range"):
                    return "set"
                if node.func.id in ("tuple", "list"):
                    return "seq"
                if node.func.id in ("len", "sum", "min", "max", "abs"):
                    return "int"
            if self.extractor._temporal_name(node.func) in ("prime", "old") and node.args:
                return self._infer_kind(node.args[0])
        if isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Slice):
            return "seq"
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.BitOr, ast.BitAnd)):
            return "set"
        return "any"

    def _state_ref(self, attr: str, primed: bool) -> str:
        if attr in self.state_subst:
            expr = self.state_subst[attr]
            if self.spec and attr in self.spec.constants:
                return expr
            return f"{expr}'" if (primed and expr.isidentifier()) else (f"({expr})'" if primed else expr)
        if self.spec and attr in self.spec.constants:
            return attr
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
            return f"{self.compile(node.value, primed=use_prime)}.{node.attr}"

        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                return f"(~({self.compile(node.operand, primed=use_prime)}))"
            if isinstance(node.op, ast.USub):
                return f"(-({self.compile(node.operand, primed=use_prime)}))"
            if isinstance(node.op, ast.UAdd):
                return self.compile(node.operand, primed=use_prime)
            raise TemporalCompileError(f"Unsupported unary op: {type(node.op).__name__}")

        if isinstance(node, ast.BoolOp):
            sep = " /\\ " if isinstance(node.op, ast.And) else " \\/ "
            return "(" + sep.join(self.compile(v, primed=use_prime) for v in node.values) + ")"

        if isinstance(node, ast.BinOp):
            return self._compile_binop(node, use_prime)

        if isinstance(node, ast.Compare):
            return self._compile_compare(node, use_prime)

        if isinstance(node, ast.IfExp):
            return (
                f"(IF {self.compile(node.test, primed=use_prime)} "
                f"THEN {self.compile(node.body, primed=use_prime)} "
                f"ELSE {self.compile(node.orelse, primed=use_prime)})"
            )

        if isinstance(node, (ast.Tuple, ast.List)):
            return "<<" + ", ".join(self.compile(e, primed=use_prime) for e in node.elts) + ">>"

        if isinstance(node, ast.Set):
            return "{" + ", ".join(self.compile(e, primed=use_prime) for e in node.elts) + "}"

        if isinstance(node, ast.Dict):
            return self._compile_dict(node, use_prime)

        if isinstance(node, ast.DictComp):
            if len(node.generators) == 1 and isinstance(node.generators[0].target, ast.Name):
                gen = node.generators[0]
                assert isinstance(gen.target, ast.Name)
                orig = gen.target.id
                safe = f"_q_{orig}" if orig in self._reserved_names() else orig
                dom = self.compile(gen.iter, primed=use_prime)
                val = self._sub(use_prime=use_prime, extra_params={orig: safe}).compile(node.value, primed=use_prime)
                return f"[{safe} \\in {dom} |-> {val}]"
            raise TemporalCompileError("Unsupported dict comprehension")

        if isinstance(node, ast.SetComp):
            if len(node.generators) == 1 and isinstance(node.generators[0].target, ast.Name):
                gen = node.generators[0]
                assert isinstance(gen.target, ast.Name)
                orig = gen.target.id
                safe = f"_q_{orig}" if orig in self._reserved_names() else orig
                dom = self.compile(gen.iter, primed=use_prime)
                sub = self._sub(use_prime=use_prime, extra_params={orig: safe})
                if gen.ifs and isinstance(node.elt, ast.Name) and node.elt.id == orig:
                    cond = " /\\ ".join(sub.compile(c, primed=use_prime) for c in gen.ifs)
                    return "{" + f"{safe} \\in {dom} : {cond}" + "}"
                if not gen.ifs:
                    return "{" + f"{sub.compile(node.elt, primed=use_prime)} : {safe} \\in {dom}" + "}"
            raise TemporalCompileError("Unsupported set comprehension")

        if isinstance(node, ast.Subscript):
            return self._compile_subscript(node, use_prime)

        if isinstance(node, ast.Call):
            return self._compile_call(node, use_prime)

        raise TemporalCompileError(f"Unsupported Python expression in specification: {ast.dump(node)}")

    def _compile_binop(self, node: ast.BinOp, use_prime: bool) -> str:
        lk, rk = self._infer_kind(node.left), self._infer_kind(node.right)
        left, right = self.compile(node.left, primed=use_prime), self.compile(node.right, primed=use_prime)
        if isinstance(node.op, ast.Add):
            if lk == "seq" or rk == "seq":
                self.needs_helpers.add("Sequences")
                return f"({left} \\o {right})"
            return f"({left} + {right})"
        if isinstance(node.op, ast.Sub):
            return f"({left} \\ {right})" if (lk == "set" or rk == "set") else f"({left} - {right})"
        if isinstance(node.op, ast.Mult):
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

    def _compile_compare(self, node: ast.Compare, use_prime: bool) -> str:
        parts: list[str] = []
        cur = node.left
        for cmp_op, nxt in zip(node.ops, node.comparators):
            lk, rk = self._infer_kind(cur), self._infer_kind(nxt)
            l_str, r_str = self.compile(cur, primed=use_prime), self.compile(nxt, primed=use_prime)
            if isinstance(cmp_op, (ast.Eq, ast.Is)):
                parts.append(f"({l_str} = {r_str})")
            elif isinstance(cmp_op, (ast.NotEq, ast.IsNot)):
                parts.append(f"({l_str} # {r_str})")
            elif isinstance(cmp_op, ast.Lt):
                if lk == "set" or rk == "set":
                    parts.append(f"(({l_str} \\subseteq {r_str}) /\\ ({l_str} # {r_str}))")
                else:
                    parts.append(f"({l_str} < {r_str})")
            elif isinstance(cmp_op, ast.LtE):
                parts.append(f"({l_str} \\subseteq {r_str})" if (lk == "set" or rk == "set") else f"({l_str} <= {r_str})")
            elif isinstance(cmp_op, ast.Gt):
                parts.append(f"({l_str} > {r_str})")
            elif isinstance(cmp_op, ast.GtE):
                parts.append(f"({l_str} >= {r_str})")
            elif isinstance(cmp_op, ast.In):
                if rk == "seq":
                    self.needs_helpers.add("Sequences")
                    parts.append(f"(\\E _idx \\in 1..Len({r_str}) : {r_str}[_idx] = {l_str})")
                else:
                    parts.append(f"({l_str} \\in {r_str})")
            elif isinstance(cmp_op, ast.NotIn):
                if rk == "seq":
                    self.needs_helpers.add("Sequences")
                    parts.append(f"(~(\\E _idx \\in 1..Len({r_str}) : {r_str}[_idx] = {l_str}))")
                else:
                    parts.append(f"({l_str} \\notin {r_str})")
            else:
                raise TemporalCompileError(f"Unsupported comparison: {type(cmp_op).__name__}")
            cur = nxt
        return parts[0] if len(parts) == 1 else "(" + " /\\ ".join(parts) + ")"

    def _compile_dict(self, node: ast.Dict, use_prime: bool) -> str:
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
        if all(isinstance(k, ast.Constant) and isinstance(k.value, str) for k in node.keys):
            pairs = []
            for k, v in zip(node.keys, node.values):
                assert isinstance(k, ast.Constant) and isinstance(k.value, str)
                pairs.append(f"{k.value} |-> {self.compile(v, primed=use_prime)}")
            return "[" + ", ".join(pairs) + "]"
        raise TemporalCompileError("Unsupported non-string dict literal")

    def _compile_subscript(self, node: ast.Subscript, use_prime: bool) -> str:
        obj_kind = self._infer_kind(node.value)
        obj = self.compile(node.value, primed=use_prime)
        if isinstance(node.slice, ast.Slice):
            self.needs_helpers.add("Sequences")
            if node.slice.lower is None:
                lower = "1"
            else:
                neg_lo = _neg_int_const(node.slice.lower)
                if neg_lo is not None:
                    lower = f"((Len({obj}) - {neg_lo}) + 1)"
                else:
                    lower = f"(({self.compile(node.slice.lower, primed=use_prime)}) + 1)"
            if node.slice.upper is None:
                upper = f"Len({obj})"
            else:
                neg_hi = _neg_int_const(node.slice.upper)
                if neg_hi is not None:
                    upper = f"(Len({obj}) - {neg_hi})"
                else:
                    upper = self.compile(node.slice.upper, primed=use_prime)
            if (
                node.slice.lower is not None
                and isinstance(node.slice.lower, ast.Constant)
                and node.slice.lower.value == 1
                and node.slice.upper is None
            ):
                return f"Tail({obj})"
            return f"SubSeq({obj}, {lower}, {upper})"
        if obj_kind == "map":
            return f"{obj}[{self.compile(node.slice, primed=use_prime)}]"
        self.needs_helpers.add("Sequences")
        neg = _neg_int_const(node.slice)
        if neg is not None:
            return f"{obj}[Len({obj})]" if neg == 1 else f"{obj}[(Len({obj}) - {neg - 1})]"
        return f"{obj}[(({self.compile(node.slice, primed=use_prime)}) + 1)]"

    def _compile_call(self, node: ast.Call, use_prime: bool) -> str:
        tname = self.extractor._temporal_name(node.func)
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
            return "(UNCHANGED <<" + ", ".join(self.compile(a, primed=False) for a in node.args) + ">>)"
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
                orig = pred.args.args[0].arg
                safe = f"_q_{orig}" if orig in self._reserved_names() else orig
                body = self._sub(use_prime=use_prime, extra_params={orig: safe}).compile(pred.body, primed=use_prime)
                return f"(CHOOSE {safe} \\in {dom} : {body})"
            raise TemporalCompileError("choose() predicate must be a 1-arg lambda")

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
                self.needs_helpers.update({"Sequences", "_Sum"})
                return f"_Sum({self.compile(node.args[0], primed=use_prime)})"
            if fname == "min" and len(node.args) == 2:
                a, b = self.compile(node.args[0], primed=use_prime), self.compile(node.args[1], primed=use_prime)
                return f"(IF {a} < {b} THEN {a} ELSE {b})"
            if fname == "max" and len(node.args) == 2:
                a, b = self.compile(node.args[0], primed=use_prime), self.compile(node.args[1], primed=use_prime)
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
                    a, b = self.compile(node.args[0], primed=use_prime), self.compile(node.args[1], primed=use_prime)
                    return f"(({a})..(({b}) - 1))"
            if fname == "tuple" and len(node.args) == 1 and isinstance(node.args[0], ast.GeneratorExp):
                return self._compile_tuple_gen(node.args[0], use_prime)
            if self.spec and fname in self.spec.pure_ops:
                args = ", ".join(self.compile(a, primed=use_prime) for a in node.args)
                return f"{fname}({args})" if args else fname

        if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and node.func.value.id == self.receiver:
            args = ", ".join(self.compile(a, primed=use_prime) for a in node.args)
            return f"{node.func.attr}({args})" if args else node.func.attr

        raise TemporalCompileError(f"Unsupported call in specification: {ast.dump(node)}")

    def _compile_action_ref(self, node: ast.expr) -> str:
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                aname = self.action_prefix + node.func.attr
            elif isinstance(node.func, ast.Name):
                aname = self.action_prefix + node.func.id
            else:
                return self.compile(node, primed=False)
            args = ", ".join(self.compile(a, primed=False) for a in node.args)
            return f"{aname}({args})" if args else aname
        if isinstance(node, ast.Attribute):
            return self.action_prefix + node.attr
        if isinstance(node, ast.Name):
            return self.action_prefix + node.id
        if isinstance(node, ast.Lambda):
            return self._compile_action_ref(node.body)
        return self.compile(node, primed=False)

    def _compile_quantifier(self, fname: str, gen: ast.GeneratorExp, use_prime: bool) -> str:
        q = "\\A" if fname == "all" else "\\E"
        reserved = self._reserved_names()
        renames: dict[str, str] = {}
        bound_specs: list[tuple[str, str, list[ast.expr]]] = []
        for comp in gen.generators:
            if not isinstance(comp.target, ast.Name):
                raise TemporalCompileError("Only simple variable targets are supported in quantifiers")
            orig = comp.target.id
            safe = f"_q_{orig}" if orig in reserved else orig
            renames[orig] = safe
            dom = self.compile(comp.iter, primed=use_prime)
            bound_specs.append((safe, dom, comp.ifs))
        sub = self._sub(use_prime=use_prime, extra_params=renames)
        body = sub.compile(gen.elt, primed=use_prime)
        for safe, dom, ifs in reversed(bound_specs):
            if ifs:
                cond = " /\\ ".join(sub.compile(c, primed=use_prime) for c in ifs)
                body = f"({cond} => {body})" if fname == "all" else f"({cond} /\\ {body})"
            body = f"({q} {safe} \\in {dom} : {body})"
        return body

    def _compile_tuple_gen(self, gen: ast.GeneratorExp, use_prime: bool) -> str:
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
                n_expr = self.compile(comp.iter.args[0], primed=use_prime)
                sub = self._sub(use_prime=use_prime, extra_params={comp.target.id: "(_i - 1)"})
                return f"[_i \\in 1..({n_expr}) |-> {sub.compile(gen.elt, primed=use_prime)}]"
        raise TemporalCompileError("Unsupported tuple generator expression")


# ---------------------------------------------------------------------------
# Imperative Body & Pure Function Compilers
# ---------------------------------------------------------------------------


def _compile_imperative_body(
    fn: ast.FunctionDef,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: dict[str, _TypeInfo],
    needs_helpers: set[str],
) -> tuple[dict[str, str], Optional[str]]:
    receiver = fn.args.args[0].arg if (not spec.is_module and fn.args.args) else None
    state_exprs: dict[str, str] = {v: v for v in (*spec.states, *spec.ghosts)}
    locals_env: dict[str, str] = {}
    local_list_copies: dict[str, str] = {}
    ret_expr: Optional[str] = None

    def mk_compiler() -> _ExprCompiler:
        return _ExprCompiler(
            extractor, spec, var_types, receiver=receiver,
            param_map=locals_env, state_subst=state_exprs, needs_helpers=needs_helpers,
        )

    def state_target_name(tgt: ast.expr) -> Optional[str]:
        if receiver is not None and isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name) and tgt.value.id == receiver:
            return tgt.attr
        if receiver is None and isinstance(tgt, ast.Name) and tgt.id in state_exprs:
            return tgt.id
        return None

    def run_stmts(stmts: list[ast.stmt]) -> None:
        nonlocal ret_expr
        for s in stmts:
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and isinstance(s.value.value, str):
                continue
            if isinstance(s, (ast.Pass, ast.Assert, ast.Global)):
                continue
            if isinstance(s, ast.Return):
                if s.value is not None:
                    ret_expr = mk_compiler().compile(s.value)
                return
            if isinstance(s, ast.Assign) and len(s.targets) == 1:
                tgt = s.targets[0]
                sname = state_target_name(tgt)
                if sname is not None:
                    if (
                        isinstance(s.value, ast.Call)
                        and isinstance(s.value.func, ast.Name)
                        and s.value.func.id == "tuple"
                        and len(s.value.args) == 1
                        and isinstance(s.value.args[0], ast.Name)
                        and s.value.args[0].id in local_list_copies
                    ):
                        state_exprs[sname] = local_list_copies[s.value.args[0].id]
                    else:
                        state_exprs[sname] = mk_compiler().compile(s.value)
                elif isinstance(tgt, ast.Name):
                    if isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Name) and s.value.func.id == "list" and len(s.value.args) == 1:
                        local_list_copies[tgt.id] = mk_compiler().compile(s.value.args[0])
                        locals_env[tgt.id] = local_list_copies[tgt.id]
                    else:
                        locals_env[tgt.id] = mk_compiler().compile(s.value)
                elif isinstance(tgt, ast.Subscript) and isinstance(tgt.value, ast.Name) and tgt.value.id in local_list_copies:
                    idx = mk_compiler().compile(tgt.slice)
                    val = mk_compiler().compile(s.value)
                    updated = f"[{local_list_copies[tgt.value.id]} EXCEPT ![({idx}) + 1] = {val}]"
                    local_list_copies[tgt.value.id] = updated
                    locals_env[tgt.value.id] = updated
                else:
                    raise TemporalCompileError(f"Unsupported assignment in {fn.name}: {ast.dump(s)}")
            elif isinstance(s, ast.AugAssign):
                sname = state_target_name(s.target)
                if sname is not None:
                    cur_node: ast.expr = (
                        ast.Attribute(value=ast.Name(id=receiver, ctx=ast.Load()), attr=sname, ctx=ast.Load())
                        if receiver is not None
                        else ast.Name(id=sname, ctx=ast.Load())
                    )
                    state_exprs[sname] = mk_compiler().compile(ast.BinOp(left=cur_node, op=s.op, right=s.value))
                else:
                    raise TemporalCompileError(f"Unsupported augmented assignment in {fn.name}")
            elif isinstance(s, ast.If):
                cond = mk_compiler().compile(s.test)
                saved = (dict(state_exprs), dict(locals_env), dict(local_list_copies), ret_expr)
                run_stmts(s.body)
                then_state, then_ret = dict(state_exprs), ret_expr
                state_exprs.clear()
                state_exprs.update(saved[0])
                locals_env.clear()
                locals_env.update(saved[1])
                local_list_copies.clear()
                local_list_copies.update(saved[2])
                ret_expr = saved[3]
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
    var_types: dict[str, _TypeInfo],
    needs_helpers: set[str],
    op_name: str,
) -> tuple[list[str], str]:
    params = [a.arg for a in fn.args.args]
    extra_defs: list[str] = []

    def compile_block(stmts: list[ast.stmt], env: dict[str, str]) -> str:
        cur_env = dict(env)

        def comp() -> _ExprCompiler:
            return _ExprCompiler(extractor, None, var_types, param_map=cur_env, needs_helpers=needs_helpers)

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
                else_expr = compile_block(s.orelse if s.orelse else stmts[idx + 1:], cur_env)
                return f"(IF {cond} THEN {then_expr} ELSE {else_expr})"
            elif isinstance(s, ast.While):
                loop_vars = sorted(cur_env.keys())
                all_args = params + [v for v in loop_vars if v not in params]
                loop_name = f"_loop_{op_name}"
                init_vals = [cur_env.get(v, v) for v in all_args]
                loop_env = {v: v for v in all_args}
                loop_cond = _ExprCompiler(
                    extractor, None, var_types, param_map=loop_env, needs_helpers=needs_helpers
                ).compile(s.test)
                after_expr = compile_block(stmts[idx + 1:], loop_env)

                def compile_loop_body(
                    body_stmts: list[ast.stmt],
                    lenv: dict[str, str],
                    _loop_name: str = loop_name,
                    _all_args: list[str] = all_args,
                ) -> str:
                    le = dict(lenv)

                    def lc() -> _ExprCompiler:
                        return _ExprCompiler(extractor, None, var_types, param_map=le, needs_helpers=needs_helpers)

                    for bi, bs in enumerate(body_stmts):
                        if isinstance(bs, ast.Return):
                            if bs.value is None:
                                needs_helpers.add("NONE")
                                return "NONE"
                            return lc().compile(bs.value)
                        if isinstance(bs, ast.Assign) and len(bs.targets) == 1 and isinstance(bs.targets[0], ast.Name):
                            le[bs.targets[0].id] = lc().compile(bs.value)
                        elif isinstance(bs, ast.AugAssign) and isinstance(bs.target, ast.Name):
                            le[bs.target.id] = lc().compile(
                                ast.BinOp(left=ast.Name(id=bs.target.id, ctx=ast.Load()), op=bs.op, right=bs.value)
                            )
                        elif isinstance(bs, ast.If):
                            c = lc().compile(bs.test)
                            t_br = compile_loop_body(bs.body, le)
                            e_br = compile_loop_body(bs.orelse if bs.orelse else body_stmts[bi + 1:], le)
                            return f"(IF {c} THEN {t_br} ELSE {e_br})"
                        else:
                            raise TemporalCompileError(f"Unsupported statement in while loop of {fn.name}")
                    return f"{_loop_name}({', '.join(le[v] for v in _all_args)})"

                step_expr = compile_loop_body(s.body, loop_env)
                extra_defs.append(f"RECURSIVE {loop_name}({', '.join('_' for _ in all_args)})")
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
# TLA+ & CFG Code Generation Helpers
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


def _collect_model_values(obj: Any, out: set[str]) -> None:
    if isinstance(obj, _ModelValueRef):
        out.add(obj.name)
    elif isinstance(obj, (_SymmetryVal, _DomainVal)):
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
    var_types: dict[str, _TypeInfo],
    needs_helpers: set[str],
    *,
    post_by_default: bool = False,
    param_map: Optional[dict[str, str]] = None,
    state_subst: Optional[dict[str, str]] = None,
    action_prefix: str = "",
) -> str:
    if isinstance(pred, ast.Lambda):
        receiver = pred.args.args[0].arg if (not spec.is_module and pred.args.args) else None
        return _ExprCompiler(
            extractor, spec, var_types, receiver=receiver, post_by_default=post_by_default,
            param_map=param_map, state_subst=state_subst, action_prefix=action_prefix,
            needs_helpers=needs_helpers,
        ).compile(pred.body)
    raise TemporalCompileError(f"Expected lambda predicate, got {type(pred).__name__}")


def _compile_func_predicate(
    fn: ast.FunctionDef,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: dict[str, _TypeInfo],
    needs_helpers: set[str],
    *,
    state_subst: Optional[dict[str, str]] = None,
) -> str:
    receiver = fn.args.args[0].arg if (not spec.is_module and fn.args.args) else None
    lets: list[tuple[str, str]] = []
    ret_expr: Optional[str] = None
    compiler = _ExprCompiler(
        extractor, spec, var_types, receiver=receiver, state_subst=state_subst, needs_helpers=needs_helpers
    )
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
        return "(LET " + "\n    ".join(f"{k} == {v}" for k, v in lets) + f" IN {ret_expr})"
    return ret_expr


def _compile_clause(
    clause: _ClauseDecl,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: dict[str, _TypeInfo],
    needs_helpers: set[str],
    *,
    state_subst: Optional[dict[str, str]] = None,
) -> Optional[str]:
    if clause.expr is not None:
        return _compile_lambda(clause.expr, extractor, spec, var_types, needs_helpers, state_subst=state_subst)
    if clause.func is not None:
        return _compile_func_predicate(
            clause.func, extractor, spec, var_types, needs_helpers, state_subst=state_subst
        )
    return None


def _compile_where(
    w: ast.expr,
    target_tla: str,
    nullable: bool,
    extractor: _ModuleExtractor,
    spec: Optional[_SpecDecl],
    var_types: dict[str, _TypeInfo],
    needs_helpers: set[str],
) -> Optional[str]:
    if not (isinstance(w, ast.Lambda) and len(w.args.args) == 1):
        return None
    expr = _ExprCompiler(
        extractor, spec, var_types, param_map={w.args.args[0].arg: target_tla}, needs_helpers=needs_helpers
    ).compile(w.body)
    if nullable:
        needs_helpers.add("NONE")
        return f"(({target_tla} # NONE) => {expr})"
    return expr


def _mentioned_next_vars(nodes: list[ast.AST], extractor: _ModuleExtractor, all_vars: set[str]) -> set[str]:
    """Return state/ghost variable names referenced inside prime(...) or unchanged(...)."""
    mentioned: set[str] = set()
    for root in nodes:
        for node in ast.walk(root):
            if isinstance(node, ast.Call) and extractor._temporal_name(node.func) in ("prime", "unchanged"):
                for arg in node.args:
                    for sub in ast.walk(arg):
                        if isinstance(sub, ast.Attribute) and sub.attr in all_vars:
                            mentioned.add(sub.attr)
                        elif isinstance(sub, ast.Name) and sub.id in all_vars:
                            mentioned.add(sub.id)
    return mentioned


def _resolve_param_domain(
    model: _ModelDecl,
    spec: _SpecDecl,
    action_name: str,
    param_name: str,
    pinfo: _TypeInfo,
) -> str:
    for key in (f"{action_name}.{param_name}", param_name, pinfo.name or ""):
        if key and key in model.domains:
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


def _fairness_subscript(vars_tuple: tuple[str, ...]) -> str:
    if not vars_tuple:
        return "_vars"
    return vars_tuple[0] if len(vars_tuple) == 1 else "<<" + ", ".join(vars_tuple) + ">>"


def _uses_old(expr: ast.expr, extractor: _ModuleExtractor) -> bool:
    return any(isinstance(n, ast.Call) and extractor._temporal_name(n.func) == "old" for n in ast.walk(expr))


def _compile_conformance_action(
    pred: ast.expr,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: dict[str, _TypeInfo],
    impl_next: dict[str, str],
    needs_helpers: set[str],
) -> str:
    assert isinstance(pred, ast.Lambda)
    receiver = pred.args.args[0].arg if (not spec.is_module and pred.args.args) else None

    class _SubstCompiler(_ExprCompiler):
        def _state_ref(self, attr: str, primed: bool) -> str:
            if primed and attr in impl_next:
                return f"({impl_next[attr]})"
            return super()._state_ref(attr, primed=False)

    return _SubstCompiler(extractor, spec, var_types, receiver=receiver, needs_helpers=needs_helpers).compile(pred.body)


def _compile_conformance_ensures(
    pred: ast.expr,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    var_types: dict[str, _TypeInfo],
    impl_next: dict[str, str],
    impl_ret: Optional[str],
    needs_helpers: set[str],
) -> str:
    assert isinstance(pred, ast.Lambda)
    receiver = pred.args.args[0].arg if (not spec.is_module and pred.args.args) else None
    pmap = {"result": impl_ret} if impl_ret is not None else {}

    class _EnsCompiler(_ExprCompiler):
        def _state_ref(self, attr: str, primed: bool) -> str:
            if primed and attr in impl_next:
                return f"({impl_next[attr]})"
            return super()._state_ref(attr, primed=False)

    return _EnsCompiler(
        extractor, spec, var_types, receiver=receiver, post_by_default=True, param_map=pmap, needs_helpers=needs_helpers
    ).compile(pred.body)


# ---------------------------------------------------------------------------
# Spec & Refinement Compiler
# ---------------------------------------------------------------------------


def _compile_refinement(
    ref: _RefineDecl,
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    model: _ModelDecl,
    var_types: dict[str, _TypeInfo],
    needs_helpers: set[str],
    body_defs: list[str],
    inv_names: list[str],
    prop_names: list[str],
) -> bool:
    if ref.target_name not in extractor.specs:
        return False
    abs_spec = extractor.specs[ref.target_name]
    abs_var_types: dict[str, _TypeInfo] = {
        d.name: d.type_info for d in (*abs_spec.constants.values(), *abs_spec.states.values(), *abs_spec.ghosts.values())
    }
    abs_subst: dict[str, str] = {}
    for abs_var, map_expr in ref.mapping.items():
        op_name = f"_Ref_{ref.name}_{abs_var}"
        compiled_map = _ExprCompiler(
            extractor, spec, var_types, receiver=ref.receiver, needs_helpers=needs_helpers
        ).compile(map_expr)
        body_defs.append(f"{op_name} == {compiled_map}")
        abs_subst[abs_var] = op_name

    # Default identity mapping for abstract vars sharing concrete names
    for abs_var in (*abs_spec.constants, *abs_spec.states, *abs_spec.ghosts):
        if abs_var not in abs_subst and abs_var in var_types:
            abs_subst[abs_var] = abs_var

    added_temporal = False

    # 1. Abstract Init refinement (state formula checked as PROPERTY -> must hold on Init)
    abs_init_parts: list[str] = []
    for a_init in abs_spec.inits:
        compiled = _compile_clause(a_init, extractor, abs_spec, abs_var_types, needs_helpers, state_subst=abs_subst)
        if compiled:
            abs_init_parts.append(compiled)
    if abs_init_parts:
        init_prop = f"_Ref_{ref.name}_Init"
        body_defs.append(f"{init_prop} == " + " /\\ ".join(abs_init_parts))
        prop_names.append(init_prop)
        added_temporal = True

    # 2. Abstract Next step simulation ([][AbsNext]_abs_vars)
    abs_state_vars = [v for v in (*abs_spec.states, *abs_spec.ghosts) if v in abs_subst]
    abs_state_ops = [abs_subst[v] for v in abs_state_vars]
    abs_step_disjuncts: list[str] = []
    for abs_act in abs_spec.actions.values():
        p_types = {**abs_var_types, **{pn: pt for pn, pt in abs_act.params}}
        parts: list[str] = []
        for req in abs_act.requires:
            parts.append(_compile_lambda(req, extractor, abs_spec, p_types, needs_helpers, state_subst=abs_subst))
        for ap in abs_act.action_preds:
            parts.append(_compile_lambda(ap, extractor, abs_spec, p_types, needs_helpers, state_subst=abs_subst))
        if abs_act.is_bool_action and abs_act.func is not None and abs_act.has_body:
            parts.append(_compile_func_predicate(abs_act.func, extractor, abs_spec, p_types, needs_helpers, state_subst=abs_subst))
        if not parts:
            continue
        if abs_act.modifies:
            mod_set = set().union(*abs_act.modifies)
            unch = [abs_subst[v] for v in abs_state_vars if v not in mod_set]
        elif abs_act.unchanged:
            unch_names = set().union(*abs_act.unchanged)
            unch = [abs_subst[v] for v in abs_state_vars if v in unch_names]
        else:
            ast_sources: list[ast.AST] = list(abs_act.action_preds)
            if abs_act.func is not None and abs_act.has_body:
                ast_sources.append(abs_act.func)
            mentioned = _mentioned_next_vars(ast_sources, extractor, set(abs_state_vars))
            unch = [abs_subst[v] for v in abs_state_vars if v not in mentioned]
        if unch:
            parts.append(f"UNCHANGED <<{', '.join(unch)}>>")
        act_expr = "(" + " /\\ ".join(f"({p})" for p in parts) + ")"
        for pn, pt in reversed(abs_act.params):
            dom = _resolve_param_domain(model, spec, abs_act.name, pn, pt)
            act_expr = f"(\\E {pn} \\in {dom} : {act_expr})"
        abs_step_disjuncts.append(act_expr)
    if abs_step_disjuncts and abs_state_ops:
        abs_vars_name = f"_Ref_{ref.name}_vars"
        body_defs.append(f"{abs_vars_name} == <<" + ", ".join(abs_state_ops) + ">>")
        step_prop = f"_Ref_{ref.name}_Step"
        body_defs.append(f"{step_prop} == [][" + " \\/ ".join(abs_step_disjuncts) + f"]_{abs_vars_name}")
        prop_names.append(step_prop)
        added_temporal = True

    # 3. Abstract Invariants
    for abs_inv in abs_spec.invariants:
        compiled = _compile_clause(abs_inv, extractor, abs_spec, abs_var_types, needs_helpers, state_subst=abs_subst)
        if compiled:
            a_inv_name = f"_Ref_{ref.name}_{abs_inv.name}"
            body_defs.append(f"{a_inv_name} == {compiled}")
            inv_names.append(a_inv_name)

    # 4. Abstract Temporal Properties
    for abs_prop in abs_spec.properties:
        compiled = _compile_clause(abs_prop, extractor, abs_spec, abs_var_types, needs_helpers, state_subst=abs_subst)
        if compiled:
            a_prop_name = f"_Ref_{ref.name}_{abs_prop.name}"
            body_defs.append(f"{a_prop_name} == {compiled}")
            prop_names.append(a_prop_name)
            added_temporal = True

    return added_temporal


def _compile_spec_model(
    extractor: _ModuleExtractor,
    spec: _SpecDecl,
    model: _ModelDecl,
    *,
    mode: str = "all",
    source_path: Optional[str] = None,
) -> CompiledModel:
    mod_name = _sanitize_ident(f"{spec.name}_{model.name}" if model.name != spec.name else spec.name)
    needs_helpers: set[str] = {"Integers"}
    all_vars = list(spec.states.keys()) + list(spec.ghosts.keys())
    all_vars_set = set(all_vars)
    var_types: dict[str, _TypeInfo] = {
        d.name: d.type_info for d in (*spec.constants.values(), *spec.states.values(), *spec.ghosts.values())
    }
    for p in spec.pure_ops.values():
        var_types[p.name] = p.return_type

    cfg_constants: list[str] = []
    model_values: set[str] = set()
    _collect_model_values(model.constants, model_values)
    _collect_model_values(model.domains, model_values)

    const_names = list(spec.constants.keys())
    sym_sets: list[tuple[str, _SymmetryVal]] = []
    seen_sym: list[_SymmetryVal] = []

    for cname in const_names:
        if cname in model.constants:
            cval = model.constants[cname]
            cfg_constants.append(f"  {cname} = {_format_cfg_value(cval)}")
            if isinstance(cval, _SymmetryVal) and cval not in seen_sym:
                seen_sym.append(cval)
                sym_sets.append((cname, cval))
        else:
            default_node = spec.constants[cname].default
            if default_node is not None:
                cval = extractor._eval_const(default_node)
                cfg_constants.append(f"  {cname} = {_format_cfg_value(cval)}")

    for dkey, dval in model.domains.items():
        if isinstance(dval, _SymmetryVal) and dval not in seen_sym:
            seen_sym.append(dval)
            sym_cname = _sanitize_ident(f"_SYM_{dkey}")
            const_names.append(sym_cname)
            cfg_constants.append(f"  {sym_cname} = {_format_cfg_value(dval)}")
            sym_sets.append((sym_cname, dval))
            model = _ModelDecl(**{**model.__dict__, "constants": {**model.constants, sym_cname: dval}})

    for s in model.symmetry:
        if s not in seen_sym:
            seen_sym.append(s)
            sym_cname = f"_SYM_{len(sym_sets)}"
            const_names.append(sym_cname)
            cfg_constants.append(f"  {sym_cname} = {_format_cfg_value(s)}")
            sym_sets.append((sym_cname, s))

    body_defs: list[str] = []

    # Pure helper operators
    for pname, pdecl in spec.pure_ops.items():
        p_expr = _compile_func_predicate(pdecl.func, extractor, spec, var_types, needs_helpers)
        pargs = ", ".join(p for p, _ in pdecl.params)
        body_defs.append(f"{pname}({pargs}) == {p_expr}" if pargs else f"{pname} == {p_expr}")

    # Assumptions
    for a in spec.assumptions:
        compiled = _compile_clause(a, extractor, spec, var_types, needs_helpers)
        if compiled:
            body_defs.append(f"ASSUME {compiled}")
    for cdecl in spec.constants.values():
        for w in cdecl.type_info.wheres:
            w_expr = _compile_where(w, cdecl.name, cdecl.type_info.nullable, extractor, spec, var_types, needs_helpers)
            if w_expr:
                body_defs.append(f"ASSUME {w_expr}")

    # Init
    init_parts: list[str] = []
    for idecl in spec.inits:
        if model.init_override and idecl.name != model.init_override:
            continue
        compiled = _compile_clause(idecl, extractor, spec, var_types, needs_helpers)
        if compiled:
            init_parts.append(compiled)
    if not init_parts:
        for vname in all_vars:
            vdecl = spec.states.get(vname) or spec.ghosts[vname]
            if vdecl.default is not None:
                val = _ExprCompiler(extractor, spec, var_types, needs_helpers=needs_helpers).compile(vdecl.default)
                init_parts.append(f"({vname} = {val})")
    body_defs.append("Init == " + (" /\\ ".join(init_parts) if init_parts else "TRUE"))

    # Actions
    selected_actions = (
        [a for n, a in spec.actions.items() if n in model.actions_override]
        if model.actions_override is not None
        else list(spec.actions.values())
    )
    next_disjuncts: list[str] = []
    conformance_checks: list[tuple[str, str]] = []
    preserves_props: list[tuple[str, str]] = []
    fairness_parts: list[str] = []
    prop_names: list[str] = []
    has_fairness_or_liveness = bool(spec.fairness or spec.properties)

    for act in selected_actions:
        p_types = {**var_types, **{pn: pt for pn, pt in act.params}}
        guards: list[str] = []
        for pn, pt in act.params:
            for w in pt.wheres:
                w_expr = _compile_where(w, pn, pt.nullable, extractor, spec, p_types, needs_helpers)
                if w_expr:
                    guards.append(w_expr)
        for req in act.requires:
            guards.append(_compile_lambda(req, extractor, spec, p_types, needs_helpers))

        use_impl_body = (
            mode != "spec-only"
            and act.has_body
            and act.func is not None
            and not act.is_bool_action
        )

        trans_parts: list[str] = list(guards)
        if use_impl_body:
            assert act.func is not None
            impl_next, impl_ret = _compile_imperative_body(act.func, extractor, spec, p_types, needs_helpers)
            # Extract ghost updates from Action(pred) when ghost vars are not assigned in Python body
            for ap in act.action_preds:
                if isinstance(ap, ast.Lambda):
                    receiver = ap.args.args[0].arg if (not spec.is_module and ap.args.args) else None
                    for eq_node in ast.walk(ap.body):
                        if isinstance(eq_node, ast.Compare) and len(eq_node.ops) == 1 and isinstance(eq_node.ops[0], ast.Eq):
                            lhs = eq_node.left
                            if isinstance(lhs, ast.Call) and extractor._temporal_name(lhs.func) == "prime" and len(lhs.args) == 1:
                                arg = lhs.args[0]
                                gname = arg.attr if isinstance(arg, ast.Attribute) else (arg.id if isinstance(arg, ast.Name) else None)
                                if gname and gname in spec.ghosts and impl_next[gname] == gname:
                                    impl_next[gname] = _ExprCompiler(
                                        extractor, spec, p_types, receiver=receiver, needs_helpers=needs_helpers
                                    ).compile(eq_node.comparators[0])

            for v in all_vars:
                trans_parts.append(f"(UNCHANGED {v})" if impl_next[v] == v else f"({v}' = {impl_next[v]})")

            # Conformance obligations (Action, Ensures, Preserves, return Where, Modifies/Unchanged)
            ob_parts: list[str] = []
            for ap in act.action_preds:
                ob_parts.append(_compile_conformance_action(ap, extractor, spec, p_types, impl_next, needs_helpers))
            for ens in act.ensures:
                pmap = {"result": impl_ret} if impl_ret is not None else {}
                if _uses_old(ens, extractor):
                    ob_parts.append(_compile_conformance_ensures(ens, extractor, spec, p_types, impl_next, impl_ret, needs_helpers))
                else:
                    ob_parts.append(
                        _compile_lambda(ens, extractor, spec, p_types, needs_helpers, param_map=pmap, state_subst=impl_next)
                    )
            for pres in act.preserves:
                pre_p = _compile_lambda(pres, extractor, spec, p_types, needs_helpers)
                post_p = _compile_lambda(pres, extractor, spec, p_types, needs_helpers, state_subst=impl_next)
                ob_parts.append(f"({pre_p} => {post_p})")
            if impl_ret is not None:
                for w in act.return_type.wheres:
                    w_expr = _compile_where(w, impl_ret, act.return_type.nullable, extractor, spec, p_types, needs_helpers)
                    if w_expr:
                        ob_parts.append(w_expr)
            # Frame conformance
            frame_unchanged: set[str] = set()
            if act.modifies:
                allowed = set(all_vars)
                for mset in act.modifies:
                    allowed &= set(mset)
                frame_unchanged |= all_vars_set - allowed
            for uset in act.unchanged:
                frame_unchanged |= set(uset) & all_vars_set
            for fv in sorted(frame_unchanged):
                if impl_next[fv] != fv:
                    ob_parts.append(f"({impl_next[fv]} = {fv})")

            if ob_parts:
                guard_str = " /\\ ".join(guards) if guards else "TRUE"
                ob_expr = f"({guard_str} => (" + " /\\ ".join(ob_parts) + "))"
                for pn, pt in reversed(act.params):
                    dom = _resolve_param_domain(model, spec, act.name, pn, pt)
                    ob_expr = f"(\\A {pn} \\in {dom} : {ob_expr})"
                conformance_checks.append((f"_Conform_{act.name}", ob_expr))
        else:
            ast_sources: list[ast.AST] = []
            if act.action_preds:
                for ap in act.action_preds:
                    trans_parts.append(_compile_lambda(ap, extractor, spec, p_types, needs_helpers))
                    ast_sources.append(ap)
            elif act.func is not None and act.has_body:
                trans_parts.append(_compile_func_predicate(act.func, extractor, spec, p_types, needs_helpers))
                ast_sources.append(act.func)

            unchanged_vars: set[str] = set()
            if act.modifies:
                allowed = set(all_vars)
                for mset in act.modifies:
                    allowed &= set(mset)
                unchanged_vars |= all_vars_set - allowed
            elif ast_sources:
                # Implicit framing for unmentioned state/ghost variables
                unchanged_vars |= all_vars_set - _mentioned_next_vars(ast_sources, extractor, all_vars_set)
            for uset in act.unchanged:
                unchanged_vars |= set(uset) & all_vars_set
            for uv in sorted(unchanged_vars):
                trans_parts.append(f"(UNCHANGED {uv})")

            # Preserves obligations on declarative actions (emitted after _vars)
            for idx, pres in enumerate(act.preserves):
                pre_p = _compile_lambda(pres, extractor, spec, p_types, needs_helpers)
                post_p = _compile_lambda(pres, extractor, spec, p_types, needs_helpers, post_by_default=True)
                pname = f"_Preserves_{act.name}_{idx}"
                act_ref = f"{act.name}(" + ", ".join(p for p, _ in act.params) + ")" if act.params else act.name
                prop_body = f"({act_ref} => ({pre_p} => {post_p}))"
                for pn, pt in reversed(act.params):
                    dom = _resolve_param_domain(model, spec, act.name, pn, pt)
                    prop_body = f"(\\A {pn} \\in {dom} : {prop_body})"
                preserves_props.append((pname, prop_body))
                has_fairness_or_liveness = True

        act_body = " /\\ ".join(trans_parts) if trans_parts else "TRUE"
        if act.params:
            pargs = ", ".join(p for p, _ in act.params)
            body_defs.append(f"{act.name}({pargs}) == {act_body}")
            quant = f"{act.name}({pargs})"
            for pn, pt in reversed(act.params):
                dom = _resolve_param_domain(model, spec, act.name, pn, pt)
                quant = f"(\\E {pn} \\in {dom} : {quant})"
            next_disjuncts.append(quant)
            fair_target = quant
        else:
            body_defs.append(f"{act.name} == {act_body}")
            next_disjuncts.append(act.name)
            fair_target = act.name

        for wf in act.weak_fairness:
            fairness_parts.append(f"WF_{_fairness_subscript(wf)}({fair_target})")
            has_fairness_or_liveness = True
        for sf in act.strong_fairness:
            fairness_parts.append(f"SF_{_fairness_subscript(sf)}({fair_target})")
            has_fairness_or_liveness = True

    body_defs.append("Next == " + (" \\/ ".join(next_disjuncts) if next_disjuncts else "FALSE"))
    body_defs.append("_vars == <<" + ", ".join(all_vars) + ">>")

    for pname, prop_body in preserves_props:
        body_defs.append(f"{pname} == [][{prop_body}]__vars")
        prop_names.append(pname)

    for fair_clause in spec.fairness:
        compiled = _compile_clause(fair_clause, extractor, spec, var_types, needs_helpers)
        if compiled:
            fairness_parts.append(compiled)

    # Invariants
    inv_names: list[str] = []
    for inv in spec.invariants:
        if model.invariants_override is not None and inv.name not in model.invariants_override:
            continue
        compiled = _compile_clause(inv, extractor, spec, var_types, needs_helpers)
        if compiled:
            body_defs.append(f"{inv.name} == {compiled}")
            inv_names.append(inv.name)

    for vname in all_vars:
        vdecl = spec.states.get(vname) or spec.ghosts[vname]
        for idx, w in enumerate(vdecl.type_info.wheres):
            w_expr = _compile_where(w, vname, vdecl.type_info.nullable, extractor, spec, var_types, needs_helpers)
            if w_expr:
                wname = f"_Type_{vname}_{idx}"
                body_defs.append(f"{wname} == {w_expr}")
                inv_names.append(wname)

    for cname, cexpr in conformance_checks:
        body_defs.append(f"{cname} == {cexpr}")
        inv_names.append(cname)

    # Action invariants & Temporal properties
    for ainv in spec.action_invariants:
        compiled = _compile_clause(ainv, extractor, spec, var_types, needs_helpers)
        if compiled:
            body_defs.append(f"{ainv.name} == [][{compiled}]__vars")
            prop_names.append(ainv.name)
            has_fairness_or_liveness = True

    for prop in spec.properties:
        if model.properties_override is not None and prop.name not in model.properties_override:
            continue
        compiled = _compile_clause(prop, extractor, spec, var_types, needs_helpers)
        if compiled:
            body_defs.append(f"{prop.name} == {compiled}")
            prop_names.append(prop.name)
            has_fairness_or_liveness = True

    # Full refinement checking
    for ref in spec.refinements:
        if _compile_refinement(ref, extractor, spec, model, var_types, needs_helpers, body_defs, inv_names, prop_names):
            has_fairness_or_liveness = True

    # Model-level constraints, view, alias, postcondition
    for attr, tla_name in (
        ("state_constraint", "_Constraint"),
        ("action_constraint", "_ActionConstraint"),
        ("view", "_View"),
        ("alias", "_Alias"),
        ("postcondition", "_Postcondition"),
    ):
        expr_node = getattr(model, attr)
        if expr_node is not None:
            body_defs.append(f"{tla_name} == {_compile_lambda(expr_node, extractor, spec, var_types, needs_helpers)}")

    use_symmetry = bool(sym_sets) and not prop_names
    if use_symmetry:
        needs_helpers.add("TLC")
        body_defs.append("_Symmetry == " + " \\cup ".join(f"Permutations({cname})" for cname, _ in sym_sets))

    if has_fairness_or_liveness:
        body_defs.append("Spec == " + " /\\ ".join(["Init", "[][Next]__vars", *fairness_parts]))

    extends = [m for m in ("Integers", "Sequences", "FiniteSets", "TLC") if m in needs_helpers]
    if "NONE" in needs_helpers:
        model_values.add("NONE")
    for mv in sorted(model_values):
        if mv not in const_names:
            const_names.append(mv)
            cfg_constants.append(f"  {mv} = {mv}")

    lines = [f"---- MODULE {mod_name} ----"]
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

    cfg_lines = ["SPECIFICATION Spec"] if has_fairness_or_liveness else ["INIT Init", "NEXT Next"]
    if cfg_constants:
        cfg_lines.append("CONSTANTS")
        cfg_lines.extend(cfg_constants)
    cfg_lines.extend(f"INVARIANT {n}" for n in inv_names)
    cfg_lines.extend(f"PROPERTY {n}" for n in prop_names)
    for attr, directive, tla_name in (
        ("state_constraint", "CONSTRAINT", "_Constraint"),
        ("action_constraint", "ACTION_CONSTRAINT", "_ActionConstraint"),
        ("view", "VIEW", "_View"),
        ("alias", "ALIAS", "_Alias"),
        ("postcondition", "POSTCONDITION", "_Postcondition"),
    ):
        if getattr(model, attr) is not None:
            cfg_lines.append(f"{directive} {tla_name}")
    if use_symmetry:
        cfg_lines.append("SYMMETRY _Symmetry")
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


def _compile_standalone_function_model(
    extractor: _ModuleExtractor,
    fn: _PureDecl,
    *,
    model: Optional[_ModelDecl] = None,
    source_path: Optional[str] = None,
) -> CompiledModel:
    label = model.name if model is not None else fn.name
    mod_name = _sanitize_ident(f"Fn_{label}")
    needs_helpers: set[str] = {"Integers"}
    var_types = dict(fn.params)
    extra_defs, body_expr = _compile_pure_function(fn.func, extractor, var_types, needs_helpers, fn.name)

    pargs = ", ".join(p for p, _ in fn.params)
    call_expr = f"{fn.name}({pargs})" if pargs else fn.name

    def param_domain(pn: str, pt: _TypeInfo) -> str:
        if model is not None:
            for key in (f"{fn.name}.{pn}", pn, pt.name or ""):
                if key and key in model.domains:
                    return _format_domain_tla(model.domains[key])
        if pt.kind == "int":
            return "(0..6)" if pt.wheres else "(-3..3)"
        if pt.kind == "bool":
            return "BOOLEAN"
        if pt.kind == "seq":
            needs_helpers.add("Sequences")
            return "{<<>>, <<1>>, <<1, 3>>, <<1, 3, 5>>, <<2, 2, 4>>}"
        return "{0, 1, 2}"

    arg_map = {p: f"_arg_{p}" for p, _ in fn.params}
    pre_parts: list[str] = []
    for pn, pt in fn.params:
        for w in pt.wheres:
            w_expr = _compile_where(w, arg_map[pn], pt.nullable, extractor, None, var_types, needs_helpers)
            if w_expr:
                pre_parts.append(w_expr)
    for req in fn.requires:
        if isinstance(req, ast.Lambda):
            pre_parts.append(_ExprCompiler(extractor, None, var_types, param_map=arg_map, needs_helpers=needs_helpers).compile(req.body))

    post_parts: list[str] = []
    for w in fn.return_type.wheres:
        w_expr = _compile_where(w, "result", fn.return_type.nullable, extractor, None, var_types, needs_helpers)
        if w_expr:
            post_parts.append(w_expr)
    for ens in fn.ensures:
        if isinstance(ens, ast.Lambda):
            post_parts.append(_ExprCompiler(extractor, None, var_types, param_map=arg_map, needs_helpers=needs_helpers).compile(ens.body))

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
        dom_parts = [f"({arg_map[pn]} \\in {param_domain(pn, pt)})" for pn, pt in fn.params] + pre_parts
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
        name=label,
        module_name=mod_name,
        tla="\n".join(lines) + "\n",
        cfg="\n".join(cfg_lines) + "\n",
        source=source_path,
        spec_name=fn.name,
        model_name=model.name if model is not None else None,
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
) -> list[CompiledModel]:
    """Compile Temporal declarations in Python source text to TLA+ models."""
    tree = ast.parse(source, filename=source_path or "<temporal>")
    extractor = _ModuleExtractor(tree, source_path=source_path)
    extractor.extract()

    compiled: list[CompiledModel] = []
    modeled_functions: set[str] = set()

    if extractor.models:
        for m in extractor.models:
            if model is not None and m.name != model:
                continue
            if spec is not None and m.spec_name != spec:
                continue
            if m.spec_name in extractor.specs:
                compiled.append(
                    _compile_spec_model(extractor, extractor.specs[m.spec_name], m, mode=mode, source_path=source_path)
                )
            elif m.spec_name in extractor.functions:
                modeled_functions.add(m.spec_name)
                compiled.append(
                    _compile_standalone_function_model(extractor, extractor.functions[m.spec_name], model=m, source_path=source_path)
                )
            else:
                raise TemporalCompileError(
                    f"Model {m.name!r} references unknown specification {m.spec_name!r}"
                )
    elif extractor.specs:
        for sname, sdecl in extractor.specs.items():
            if spec is not None and sname != spec:
                continue
            if sdecl.is_protocol and any(not other.is_protocol for other in extractor.specs.values()):
                continue
            default_model = _ModelDecl(name=sname, spec_name=sname)
            compiled.append(
                _compile_spec_model(extractor, sdecl, default_model, mode=mode, source_path=source_path)
            )

    if model is None:
        for fn_name, fn in extractor.functions.items():
            if fn_name in modeled_functions:
                continue
            if spec is not None and fn_name != spec:
                continue
            compiled.append(_compile_standalone_function_model(extractor, fn, source_path=source_path))

    return compiled


def compile_file(
    path: Union[str, Path],
    *,
    spec: Optional[str] = None,
    model: Optional[str] = None,
    mode: str = "all",
) -> list[CompiledModel]:
    """Read a Python file and compile all Temporal models/contracts in it."""
    p = Path(path)
    return compile_source(
        p.read_text(encoding="utf-8"),
        source_path=str(p),
        spec=spec,
        model=model,
        mode=mode,
    )
