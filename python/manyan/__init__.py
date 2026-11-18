"""Manyan, a fast model checker for TLA+. The wheel installs the executable
itself onto the PATH; find_manyan_bin gives where, and run runs it, giving
what the check found as values."""
import json
import os
import subprocess
import sys
import sysconfig
import tempfile
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
