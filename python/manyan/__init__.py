"""Manyan, a fast model checker for TLA+. The wheel installs the executable
itself onto the PATH; find_manyan_bin gives where, and run runs it, giving
what the check found as values. check does the same in this process, with
the library beside this file, through manyan.h."""
import ctypes
import json
import os
import subprocess
import sys
import sysconfig
import tempfile
import threading
from dataclasses import dataclass
from typing import Any, Optional


def find_manyan_bin():
    """The path of the manyan executable this package installed."""
    name = "manyan.exe" if sys.platform == "win32" else "manyan"
    schemes = [sysconfig.get_default_scheme()] if hasattr(sysconfig, "get_default_scheme") else []
    schemes.append(os.name + "_user")
    for scheme in schemes:
        path = os.path.join(sysconfig.get_path("scripts", scheme), name)
        if os.path.isfile(path):
            return path
    raise FileNotFoundError(name)


class Function(dict):
    """A TLA+ function, a record among them: a dict, hashable as a TLA+
    value is, so that a set holds it. Do not change one."""

    def __hash__(self):
        return hash(frozenset(self.items()))


class Printed(str):
    """A TLA+ value Python has no form for, such as a model value: TLC's text of it."""


@dataclass
class Result:
    """What the check found, as manyan.h's ManyanResult gives it."""
    states: list    # the first counterexample printed whole: each a Function of the variables that have a value
    actions: list   # the step into each state, as TLCGet("action") gives it; with a loop, one more steps back
    loop: int       # the state, from 1, the last steps back to: its own where it stutters; 0 for none
    violated: list  # the invariants and properties the report names violated
    generated: Optional[int]  # the counts reported last; None where none is
    distinct: Optional[int]
    left: Optional[int]
    depth: Optional[int]


@dataclass
class Run:
    status: int                # the exit status, TLC's: 0, or 12 for a violated invariant, ...
    output: str                # what manyan printed, standard output and error in order
    result: Optional[Result]   # None where no check began, as for a usage error


def value(x: Any) -> Any:
    """A TLA+ value from its JSON (-result): a boolean, integer or string as
    itself, a tuple a tuple, a set a frozenset, a function a Function; any
    other a Printed."""
    if isinstance(x, list):
        return tuple(value(e) for e in x)
    if not isinstance(x, dict):
        return x
    if "#set" in x:
        return frozenset(value(e) for e in x["#set"])
    if "#map" in x:
        return Function((value(k), value(v)) for k, v in x["#map"])
    if "#tla" in x:
        return Printed(x["#tla"])
    return Function((k, value(v)) for k, v in x.items())


def run(args, cwd=None, stdin=None):
    """Run manyan with the command line args in the directory cwd: its exit
    status, its output and what the check found."""
    fd, path = tempfile.mkstemp(suffix=".json")
    os.close(fd)
    try:
        done = subprocess.run([find_manyan_bin(), "-result", path, *args], cwd=cwd, input=stdin,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        with open(path, encoding="utf-8") as f:
            text = f.read()
    finally:
        os.remove(path)
    r = json.loads(text) if text else None
    if r is not None:
        r = Result(**{**r, "states": list(value(r["states"])), "actions": list(value(r["actions"]))})
    return Run(done.returncode, done.stdout, r)


def find_manyan_lib():
    """The path of the library this package installed: manyan.c built to link."""
    name = {"darwin": "libmanyan.dylib", "win32": "manyan.dll"}.get(sys.platform, "libmanyan.so")
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    if os.path.isfile(path):
        return path
    raise FileNotFoundError(name)


class _Result(ctypes.Structure):   # manyan.h's ManyanResult
    _fields_ = [("length", ctypes.c_size_t), ("states", ctypes.POINTER(ctypes.c_void_p)),
                ("actions", ctypes.POINTER(ctypes.c_void_p)), ("loop", ctypes.c_size_t),
                ("violated", ctypes.POINTER(ctypes.c_char_p)), ("generated", ctypes.c_int64),
                ("distinct", ctypes.c_int64), ("left", ctypes.c_int64), ("depth", ctypes.c_int64)]


_Strings = ctypes.POINTER(ctypes.c_char_p)


class _Options(ctypes.Structure):   # manyan.h's ManyanOptions, in its order
    _fields_ = [("spec", ctypes.c_char_p), ("config", ctypes.c_char_p), ("check_deadlock", ctypes.c_int),
                ("dump", ctypes.c_char_p), ("dump_actions", ctypes.c_int), ("nowarning", ctypes.c_int),
                ("difftrace", ctypes.c_int), ("view", ctypes.c_int), ("keep_going", ctypes.c_int),
                ("stack", ctypes.c_int), ("user_file", ctypes.c_char_p), ("workers", ctypes.c_int),
                ("simulate", ctypes.c_int), ("generate", ctypes.c_int), ("traces", ctypes.c_long),
                ("depth", ctypes.c_long), ("seed", ctypes.c_longlong), ("seed_given", ctypes.c_int),
                ("fp", ctypes.c_int), ("aril", ctypes.c_longlong), ("trace_file", ctypes.c_char_p),
                ("properties", _Strings), ("symbolic", ctypes.c_int), ("length", ctypes.c_long),
                ("cinit", ctypes.c_char_p), ("max_error", ctypes.c_long), ("run_dir", ctypes.c_char_p),
                ("typecheck", ctypes.c_int), ("lint", ctypes.c_int), ("fmt", ctypes.c_int), ("invariants", _Strings), ("postconditions", _Strings),
                ("dump_trace", ctypes.c_char_p), ("no_te_spec", ctypes.c_int), ("result", ctypes.POINTER(_Result))]


_lib = None
_lock = threading.Lock()   # a process checks one model at a time
_BOOL, _INT, _STRING, _MODEL, _TUPLE, _FUNCTION, _SET = range(7)   # ManyanKind


def _load():
    global _lib
    if _lib is None:
        lib = ctypes.CDLL(find_manyan_lib())
        vp, size = ctypes.c_void_p, ctypes.c_size_t
        for name, res, args in [("manyan_check", ctypes.c_int, [ctypes.POINTER(_Options)]),
                                ("manyan_std_init", ctypes.c_int, []), ("manyan_kind", ctypes.c_int, [vp]),
                                ("manyan_is_true", ctypes.c_int, [vp]), ("manyan_int_value", ctypes.c_int64, [vp]),
                                ("manyan_string_value", ctypes.c_void_p, [vp, ctypes.POINTER(size)]),
                                ("manyan_size", size, [vp]), ("manyan_key", vp, [vp, size]),
                                ("manyan_value", vp, [vp, size]), ("manyan_elements", vp, [vp]),
                                ("manyan_element", vp, [vp, size]), ("manyan_print", ctypes.c_char_p, [vp])]:
            f = getattr(lib, name)
            f.restype, f.argtypes = res, args
        if lib.manyan_std_init():
            raise MemoryError("manyan_std_init")
        _lib = lib
    return _lib


def _value(lib, v):
    """A TLA+ value from manyan.h's, as value gives it from JSON."""
    kind = lib.manyan_kind(v)
    if kind == _BOOL:
        return bool(lib.manyan_is_true(v))
    if kind == _INT:
        return lib.manyan_int_value(v)
    if kind == _STRING:
        n = ctypes.c_size_t()
        return ctypes.string_at(lib.manyan_string_value(v, ctypes.byref(n)), n.value).decode()
    if kind == _TUPLE:
        return tuple(_value(lib, lib.manyan_value(v, i)) for i in range(lib.manyan_size(v)))
    if kind == _FUNCTION:
        return Function((_value(lib, lib.manyan_key(v, i)), _value(lib, lib.manyan_value(v, i)))
                        for i in range(lib.manyan_size(v)))
    e = lib.manyan_elements(v) if kind == _SET else None
    if e:
        return frozenset(_value(lib, lib.manyan_element(e, i)) for i in range(lib.manyan_size(e)))
    return Printed(lib.manyan_print(v).decode())


def _strings(xs, keep):
    a = (ctypes.c_char_p * (len(xs) + 1))(*[x.encode() for x in xs], None)
    keep.append(a)
    return a


def check(spec, **options):
    """Check the model spec (a path, with or without .tla) in this process:
    its exit status, what it printed and what it found. options are those
    of manyan.h's ManyanOptions, by name: config="M.cfg", workers=4,
    check_deadlock=False, invariants=["x < 3"], seed=1, ... Its output is
    standard output's and error's, which it holds for the check."""
    keep = []
    o = _Options(spec=os.fsencode(spec), check_deadlock=1)
    for name, x in options.items():
        if name not in dict(_Options._fields_) or name in ("spec", "seed_given", "result"):
            raise TypeError(f"check() got an unexpected keyword argument {name!r}")
        if name == "seed":
            o.seed_given = x is not None
            x = x or 0
        if isinstance(x, (list, tuple)):
            x = _strings(x, keep)
        elif isinstance(x, (str, os.PathLike)):
            x = os.fsencode(x)
        setattr(o, name, x)
    r = _Result()
    o.result = ctypes.pointer(r)
    with _lock:
        lib = _load()
        sys.stdout.flush(), sys.stderr.flush()
        with tempfile.TemporaryFile() as out:
            saved = os.dup(1), os.dup(2)
            os.dup2(out.fileno(), 1), os.dup2(out.fileno(), 2)
            try:
                status = lib.manyan_check(ctypes.byref(o))   # which flushes what it printed
            finally:
                os.dup2(saved[0], 1), os.dup2(saved[1], 2)
                os.close(saved[0]), os.close(saved[1])
            out.seek(0)
            output = out.read().decode(errors="replace")
        violated = []
        while r.violated[len(violated)]:
            violated.append(r.violated[len(violated)].decode())
        count = [None if c < 0 else c for c in (r.generated, r.distinct, r.left, r.depth)]
        result = Result([_value(lib, r.states[i]) for i in range(r.length)],
                        [_value(lib, r.actions[i]) for i in range(r.length + (r.loop > 0))],
                        r.loop, violated, *count)
    return Run(status, output, result)
