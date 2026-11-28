"""End-to-end tests for checking Python Temporal specifications via `manyan`."""
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))
import manyan

EXAMPLES = ROOT / "temporal" / "examples"


def _run_cli(*args):
    env = {
        **os.environ,
        "PYTHONPATH": str(ROOT / "python"),
        "MANYAN": os.environ.get("MANYAN", str(ROOT / "manyan")),
    }
    if (ROOT / "libmanyan.dylib").is_file():
        env.setdefault("MANYAN_LIB", str(ROOT / "libmanyan.dylib"))
    elif (ROOT / "libmanyan.so").is_file():
        env.setdefault("MANYAN_LIB", str(ROOT / "libmanyan.so"))
    return subprocess.run(
        [sys.executable, "-m", "manyan", *args],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )


class TestTemporalExamples(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        os.environ.setdefault("MANYAN", str(ROOT / "manyan"))
        for lib in ("libmanyan.dylib", "libmanyan.so"):
            if (ROOT / lib).is_file():
                os.environ.setdefault("MANYAN_LIB", str(ROOT / lib))
                break

    def test_die_hard_both_models_find_exact_solution(self) -> None:
        runs = manyan.check_temporal(EXAMPLES / "die_hard.py")
        self.assertEqual([r.name for r in runs], ["spec_model", "impl_model"])
        for tr in runs:
            self.assertFalse(tr.ok, tr.name)
            self.assertEqual(tr.run.status, 12)
            assert tr.run.result is not None
            self.assertEqual(tr.run.result.violated, ["not_solved"])
            self.assertEqual(len(tr.run.result.states), 7)
            self.assertEqual(tr.run.result.states[0], {"small": 0, "big": 0})
            self.assertEqual(tr.run.result.states[-1], {"small": 3, "big": 4})
            self.assertEqual(tr.run.result.distinct, 14)

    def test_bank_account_passes(self) -> None:
        runs = manyan.check_temporal(EXAMPLES / "bank_account.py")
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertEqual(runs[0].run.result.distinct, 884)

    def test_bounded_queue_refinement_passes(self) -> None:
        runs = manyan.check_temporal(EXAMPLES / "bounded_queue.py")
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertEqual(runs[0].run.result.distinct, 45)

    def test_mutex_safety_and_starvation_freedom_pass(self) -> None:
        runs = manyan.check_temporal(EXAMPLES / "mutex.py")
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertEqual(runs[0].run.result.distinct, 20)

    def test_semaphore_safety_conformance_and_liveness_pass(self) -> None:
        runs = manyan.check_temporal(EXAMPLES / "semaphore.py")
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertEqual(runs[0].run.result.distinct, 4)

    def test_two_phase_commit_passes(self) -> None:
        runs = manyan.check_temporal(EXAMPLES / "two_phase_commit.py")
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertEqual(runs[0].run.result.distinct, 160)

    def test_pure_function_contracts_pass(self) -> None:
        runs = manyan.check_temporal(EXAMPLES / "contracts.py")
        self.assertEqual([r.name for r in runs], ["integer_sqrt", "binary_search", "clamp"])
        for tr in runs:
            self.assertTrue(tr.ok, f"{tr.name}: {tr.run.output}")


class TestTemporalBugDetection(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        os.environ.setdefault("MANYAN", str(ROOT / "manyan"))
        for lib in ("libmanyan.dylib", "libmanyan.so"):
            if (ROOT / lib).is_file():
                os.environ.setdefault("MANYAN_LIB", str(ROOT / lib))
                break

    def test_catches_implementation_conformance_violation_and_spec_only_passes(self) -> None:
        buggy = """from typing import Annotated
from temporal import Action, Constant, Ensures, Init, Invariant, Model, Requires, State, prime

class Semaphore:
    capacity: Constant[int]
    available: State[int]
    init: Annotated[bool, Init(lambda s: s.available == s.capacity)]
    bounded: Annotated[bool, Invariant(lambda s: 0 <= s.available <= s.capacity)]

    def acquire(self) -> Annotated[
        bool,
        Requires(lambda s: s.available > 0),
        Action(lambda s: prime(s.available) == s.available - 1),
        Ensures(lambda s, result: result is True),
    ]:
        self.available -= 2
        return True

    def release(self) -> Annotated[
        None,
        Requires(lambda s: s.available < s.capacity),
        Action(lambda s: prime(s.available) == s.available + 1),
    ]:
        self.available += 1

m = Model(Semaphore, constants={"capacity": 3})
"""
        # Default conformance check catches the buggy body (-= 2 vs -= 1).
        runs = manyan.check_temporal(buggy)
        self.assertEqual(runs[0].run.status, 12)
        assert runs[0].run.result is not None
        self.assertIn("_Conform_acquire", runs[0].run.result.violated)

        # Spec-only mode checks the declared specification, which is valid.
        spec_runs = manyan.check_temporal(buggy, mode="spec-only")
        self.assertTrue(spec_runs[0].ok, spec_runs[0].run.output)

    def test_catches_ensures_return_violation(self) -> None:
        buggy = """from typing import Annotated
from temporal import Action, Constant, Ensures, Init, Model, Requires, State, prime

class S:
    n: Constant[int]
    x: State[int]
    init: Annotated[bool, Init(lambda s: s.x == 0)]

    def inc(self) -> Annotated[
        int,
        Requires(lambda s: s.x < s.n),
        Action(lambda s: prime(s.x) == s.x + 1),
        Ensures(lambda s, result: result == s.x),
    ]:
        self.x += 1
        return 0

m = Model(S, constants={"n": 2}, check_deadlock=False)
"""
        runs = manyan.check_temporal(buggy)
        self.assertEqual(runs[0].run.status, 12)
        assert runs[0].run.result is not None
        self.assertIn("_Conform_inc", runs[0].run.result.violated)

    def test_catches_liveness_violation_without_fairness(self) -> None:
        unfair = """from typing import Annotated
from temporal import Action, Constant, Init, Model, Property, Requires, State, leads_to, prime

class Semaphore:
    capacity: Constant[int]
    available: State[int]
    init: Annotated[bool, Init(lambda s: s.available == s.capacity)]
    progress: Annotated[bool, Property(lambda s: leads_to(s.available == 0, s.available > 0))]

    def acquire(self) -> Annotated[
        None,
        Requires(lambda s: s.available > 0),
        Action(lambda s: prime(s.available) == s.available - 1),
    ]:
        self.available -= 1

    def release(self) -> Annotated[
        None,
        Requires(lambda s: s.available < s.capacity),
        Action(lambda s: prime(s.available) == s.available + 1),
    ]:
        self.available += 1

m = Model(Semaphore, constants={"capacity": 2})
"""
        runs = manyan.check_temporal(unfair)
        self.assertEqual(runs[0].run.status, 13)
        assert runs[0].run.result is not None
        self.assertIn("progress", runs[0].run.result.violated)

    def test_catches_buggy_pure_function_contract(self) -> None:
        buggy = """from typing import Annotated
from temporal import Ensures, Pure, Requires

def clamp(value: int, low: int, high: int) -> Annotated[
    Pure[int],
    Requires(lambda low, high: low <= high),
    Ensures(lambda value, low, high, result: low <= result <= high),
]:
    return value
"""
        runs = manyan.check_temporal(buggy)
        self.assertEqual(runs[0].run.status, 12)
        assert runs[0].run.result is not None
        self.assertIn("Contract_clamp", runs[0].run.result.violated)
        # Counterexample reports exact Python parameter names (not _arg_*).
        self.assertIn("value", runs[0].run.result.states[0])
        self.assertIn("low", runs[0].run.result.states[0])
        self.assertIn("high", runs[0].run.result.states[0])

    def test_catches_binary_search_off_by_one_and_weak_vs_strong_fairness_in_mutex(self) -> None:
        contracts = (EXAMPLES / "contracts.py").read_text(encoding="utf-8")
        buggy_bs = contracts.replace(
            "while lo <= hi:\n        mid = (lo + hi) // 2\n        if xs[mid] == target:",
            "while lo < hi:\n        mid = (lo + hi) // 2\n        if xs[mid] == target:",
        )
        r_bs = manyan.check_temporal(buggy_bs, spec="binary_search")[0]
        self.assertEqual(r_bs.run.status, 12)
        assert r_bs.run.result is not None
        self.assertEqual(r_bs.run.result.violated, ["Contract_binary_search"])
        self.assertEqual(r_bs.run.result.states[0], {"xs": (1,), "target": 1})

        # Downgrading Mutex strong_fairness -> weak_fairness produces a real starvation lasso.
        mutex = (EXAMPLES / "mutex.py").read_text(encoding="utf-8")
        weak_mutex = mutex.replace("strong_fairness(s.acquire(p))", "weak_fairness(s.acquire(p))")
        r_mux = manyan.check_temporal(weak_mutex)[0]
        self.assertEqual(r_mux.run.status, 13, r_mux.run.output)
        assert r_mux.run.result is not None
        self.assertIn("starvation_free", r_mux.run.result.violated)
        self.assertGreater(r_mux.run.result.loop, 0)

        # Removing fairness from TwoPhaseCommit fails decision_propagates.
        tpc = (EXAMPLES / "two_phase_commit.py").read_text(encoding="utf-8")
        tpc_no_fair = tpc[:tpc.index("    fair: Annotated[")] + tpc[tpc.index("    decision_propagates:"):]
        r_tpc = manyan.check_temporal(tpc_no_fair)[0]
        self.assertEqual(r_tpc.run.status, 13, r_tpc.run.output)
        assert r_tpc.run.result is not None
        self.assertIn("decision_propagates", r_tpc.run.result.violated)

    def test_external_annotated_spec_alias(self) -> None:
        src = """from typing import Annotated
from temporal import Action, Init, Invariant, Model, State, prime

class Counter:
    x: State[int]
    inc: Annotated[bool, Action(lambda s: s.x < 3 and prime(s.x) == s.x + 1)]
    reset: Annotated[bool, Action(lambda s: prime(s.x) == 0)]

SafeCounter = Annotated[
    Counter,
    Init(lambda s: s.x == 0),
    Invariant(lambda s: 0 <= s.x <= 3),
]

m = Model(SafeCounter)
"""
        runs = manyan.check_temporal(src)
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertEqual(runs[0].run.result.distinct, 4)

    def test_static_ast_analysis_never_executes_user_module(self) -> None:
        src = """raise RuntimeError("user module must never be executed during verification")
from typing import Annotated
from temporal import Action, Init, Invariant, Model, State, prime

class Safe:
    x: State[int]
    init: Annotated[bool, Init(lambda s: s.x == 0)]
    ok: Annotated[bool, Invariant(lambda s: s.x in {0, 1})]
    flip: Annotated[bool, Action(lambda s: prime(s.x) == 1 - s.x)]

m = Model(Safe)
"""
        runs = manyan.check_temporal(src)
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)

    def test_catches_refinement_step_and_init_violations(self) -> None:
        base = (EXAMPLES / "bounded_queue.py").read_text(encoding="utf-8")
        # Buggy pop removes the newest item (LIFO) instead of oldest (FIFO) -> violates _Ref_refines_queue_Step.
        lifo = base.replace(
            "self._head = (self._head + 1) % self.capacity\n        self._size -= 1",
            "self._size -= 1",
        )
        runs = manyan.check_temporal(lifo)
        self.assertEqual(runs[0].run.status, 13, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertIn("_Ref_refines_queue_Step", runs[0].run.result.violated)

        # Buggy init starts with _size == 1 -> violates _Ref_refines_queue_Init.
        bad_init = base.replace("and s._size == 0", "and s._size == 1")
        runs2 = manyan.check_temporal(bad_init)
        self.assertEqual(runs2[0].run.status, 13, runs2[0].run.output)
        assert runs2[0].run.result is not None
        self.assertIn("_Ref_refines_queue_Init", runs2[0].run.result.violated)

    def test_module_level_specification(self) -> None:
        src = """import sys
from typing import Annotated
from temporal import Action, Constant, Init, Invariant, Model, Requires, State, prime

LIMIT: Constant[int]
count: State[int]

init: Annotated[bool, Init(lambda: count == 0)]
bounded: Annotated[bool, Invariant(lambda: 0 <= count <= LIMIT)]

def step() -> Annotated[
    None,
    Requires(lambda: count < LIMIT),
    Action(lambda: prime(count) == count + 1),
]:
    count += 1

def reset() -> Annotated[
    None,
    Action(lambda: prime(count) == 0),
]:
    count = 0

m = Model(sys.modules[__name__], constants={"LIMIT": 3})
"""
        runs = manyan.check_temporal(src)
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertEqual(runs[0].run.result.distinct, 4)

    def test_negative_sequence_slicing(self) -> None:
        src = """from typing import Annotated
from temporal import Action, Constant, Domain, Ensures, Init, Invariant, Model, Requires, State, old, prime

class Stack:
    cap: Constant[int]
    items: State[tuple[int, ...]]
    init: Annotated[bool, Init(lambda s: s.items == ())]
    bounded: Annotated[bool, Invariant(lambda s: 0 <= len(s.items) <= s.cap)]

    def push(self, x: int) -> Annotated[
        None,
        Requires(lambda s, x: len(s.items) < s.cap),
        Action(lambda s, x: prime(s.items) == s.items + (x,)),
    ]:
        self.items = self.items + (x,)

    def pop(self) -> Annotated[
        int,
        Requires(lambda s: len(s.items) > 0),
        Action(lambda s: prime(s.items) == s.items[:-1]),
        Ensures(lambda s, result: result == old(s.items)[-1]),
    ]:
        top = self.items[-1]
        self.items = self.items[:-1]
        return top

m = Model(Stack, constants={"cap": 2}, domains={"x": Domain.range(1, 2)})
"""
        runs = manyan.check_temporal(src)
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)
        assert runs[0].run.result is not None
        self.assertEqual(runs[0].run.result.distinct, 7)

    def test_implicit_framing_and_frame_conformance(self) -> None:
        # Declarative action omitting Modifies implicitly leaves unmentioned `y` unchanged.
        ok_src = """from typing import Annotated
from temporal import Action, Init, Invariant, Model, State, prime

class Pair:
    x: State[int]
    y: State[int]
    init: Annotated[bool, Init(lambda s: s.x == 0 and s.y == 7)]
    y_const: Annotated[bool, Invariant(lambda s: s.y == 7)]
    flip: Annotated[bool, Action(lambda s: prime(s.x) == 1 - s.x)]

m = Model(Pair)
"""
        runs = manyan.check_temporal(ok_src)
        self.assertTrue(runs[0].ok, runs[0].run.output)

        # Imperative method mutating a variable outside Modifies("x") violates conformance.
        bad_frame = """from typing import Annotated
from temporal import Action, Init, Model, Modifies, State, prime

class Pair:
    x: State[int]
    y: State[int]
    init: Annotated[bool, Init(lambda s: s.x == 0 and s.y == 0)]

    def flip(self) -> Annotated[
        None,
        Action(lambda s: prime(s.x) == 1 - s.x),
        Modifies("x"),
    ]:
        self.x = 1 - self.x
        self.y = 1

m = Model(Pair)
"""
        bad_runs = manyan.check_temporal(bad_frame)
        self.assertEqual(bad_runs[0].run.status, 12, bad_runs[0].run.output)
        assert bad_runs[0].run.result is not None
        self.assertIn("_Conform_flip", bad_runs[0].run.result.violated)

    def test_preserves_and_nullable_where_and_standalone_model(self) -> None:
        # Nullable Where on State field allows None and checks positive when non-None.
        src = """from typing import Annotated, Optional
from temporal import Action, Init, Model, Preserves, State, Where, prime

Positive = Annotated[int, Where(lambda x: x > 0)]

class Slot:
    val: State[Optional[Positive]]
    init: Annotated[bool, Init(lambda s: s.val is None)]
    set_one: Annotated[
        bool,
        Action(lambda s: prime(s.val) == 1),
        Preserves(lambda s: s.val is None or s.val > 0),
    ]
    clear: Annotated[bool, Action(lambda s: prime(s.val) is None)]

m = Model(Slot)
"""
        runs = manyan.check_temporal(src)
        self.assertTrue(runs[0].ok, runs[0].run.output)

        # Declarative action violating Preserves fails _Preserves_...
        bad_pres = """from typing import Annotated
from temporal import Action, Init, Model, Preserves, State, prime

class Broken:
    x: State[int]
    init: Annotated[bool, Init(lambda s: s.x == 1)]
    break_pos: Annotated[
        bool,
        Action(lambda s: prime(s.x) == -1),
        Preserves(lambda s: s.x > 0),
    ]

m = Model(Broken)
"""
        bad_pres_runs = manyan.check_temporal(bad_pres)
        self.assertEqual(bad_pres_runs[0].run.status, 13, bad_pres_runs[0].run.output)
        assert bad_pres_runs[0].run.result is not None
        self.assertIn("_Preserves_break_pos_0", bad_pres_runs[0].run.result.violated)

        # Standalone pure function with explicit Model(fn, domains=...)
        fn_src = """from typing import Annotated
from temporal import Domain, Ensures, Model, Pure, Requires

def clamp(value: int, low: int, high: int) -> Annotated[
    Pure[int],
    Requires(lambda low, high: low <= high),
    Ensures(lambda value, low, high, result: low <= result <= high),
]:
    if value < low:
        return low
    if value > high:
        return high
    return value

clamp_model = Model(
    clamp,
    domains={
        "value": Domain.range(-4, 4),
        "low": Domain.range(-2, 2),
        "high": Domain.range(-2, 2),
    },
)
"""
        fn_runs = manyan.check_temporal(fn_src)
        self.assertEqual([r.name for r in fn_runs], ["clamp_model"])
        self.assertTrue(fn_runs[0].ok, fn_runs[0].run.output)

    def test_replace_model_early_return_swap_dict_ops_and_property_ensures(self) -> None:
        src = """from dataclasses import replace
from typing import Annotated
from temporal import (
    Action, Constant, Domain, Ensures, Init, Invariant, Model, Pure, Requires, State, old, prime,
)

class Store:
    keys_set: Constant[frozenset[str]]
    a: State[int]
    b: State[int]
    data: State[dict[str, int]]

    init: Annotated[
        bool,
        Init(lambda s: s.a == 1 and s.b == 2 and s.data == {k: 0 for k in s.keys_set}),
    ]
    inv: Annotated[
        bool,
        Invariant(
            lambda s: (
                s.a + s.b == 3
                and len(s.data) == len(s.keys_set)
                and all(k in s.data and s.data.get(k, -1) >= 0 for k in s.keys_set)
                and s.data.keys() == s.keys_set
                and all(v >= 0 for v in s.data.values())
            )
        ),
    ]

    @property
    def total(self) -> Pure[int]:
        return self.a + self.b

    def swap(self) -> Annotated[
        int,
        Action(lambda s: prime(s.a) == s.b and prime(s.b) == s.a),
        Ensures(lambda s, result: s.total == old(s.total) and result == s.a),
    ]:
        self.a, self.b = self.b, self.a
        return self.a

    def bump(self, k: str) -> Annotated[
        int,
        Requires(lambda s, k: k in s.keys_set),
        Action(),
        Ensures(lambda s, k, result: result == s.data[k] and result <= 2),
    ]:
        cur: int = self.data[k]
        if cur >= 2:
            return cur
        cur += 1
        d = dict(self.data)
        d[k] = cur
        self.data = d
        return cur

base_model = Model(
    Store,
    constants={"keys_set": frozenset({"k1", "k2"})},
    domains={"k": Domain.values("k1", "k2")},
)
no_deadlock_model = replace(base_model, check_deadlock=False)
"""
        runs = manyan.check_temporal(src)
        self.assertEqual([r.name for r in runs], ["base_model", "no_deadlock_model"])
        for tr in runs:
            self.assertTrue(tr.ok, f"{tr.name}: {tr.run.output}")
        self.assertNotIn("CHECK_DEADLOCK FALSE", runs[0].compiled.cfg)
        self.assertIn("CHECK_DEADLOCK FALSE", runs[1].compiled.cfg)

    def test_compile_error_includes_line_number(self) -> None:
        bad = """from typing import Annotated
from temporal import Action, Init, Model, State

class Bad:
    x: State[int]
    init: Annotated[bool, Init(lambda s: s.x == 0)]

    def step(self) -> Annotated[None, Action()]:
        for i in range(3):
            self.x += i

m = Model(Bad)
"""
        with self.assertRaises(manyan.TemporalCompileError) as ctx:
            manyan.emit_temporal(bad)
        self.assertIn("line 9:", str(ctx.exception))

    def test_model_string_overrides_for_init_actions_and_invariants(self) -> None:
        src = """from typing import Annotated
from temporal import Action, Init, Invariant, Model, State, prime

class Counter:
    x: State[int]
    init_zero: Annotated[bool, Init(lambda s: s.x == 0)]
    init_five: Annotated[bool, Init(lambda s: s.x == 5)]
    non_neg: Annotated[bool, Invariant(lambda s: s.x >= 0)]
    under_three: Annotated[bool, Invariant(lambda s: s.x < 3)]
    inc: Annotated[bool, Action(lambda s: s.x < 2 and prime(s.x) == s.x + 1)]
    reset: Annotated[bool, Action(lambda s: prime(s.x) == 0)]

ok_model = Model(Counter, init="init_zero", actions=("inc", "reset"), invariants=("non_neg", "under_three"))
fail_model = Model(Counter, init="init_five", actions=("reset",), invariants=("under_three",))
"""
        runs = manyan.check_temporal(src)
        self.assertEqual([r.name for r in runs], ["ok_model", "fail_model"])
        self.assertTrue(runs[0].ok, runs[0].run.output)
        self.assertEqual(runs[1].run.status, 12)
        assert runs[1].run.result is not None
        self.assertEqual(runs[1].run.result.violated, ["under_three"])

    def test_protocol_inheritance_conformance_without_repeating_contracts(self) -> None:
        base = """from typing import Annotated, Protocol
from temporal import Action, Constant, Domain, Ensures, Init, Invariant, Model, Modifies, Requires, State, old, prime

class BoundedQueue(Protocol):
    capacity: Constant[int]
    items: State[tuple[int, ...]]
    init: Annotated[bool, Init(lambda s: s.items == ())]
    bounded: Annotated[bool, Invariant(lambda s: 0 <= len(s.items) <= s.capacity)]

    def push(self, item: int) -> Annotated[
        None,
        Requires(lambda s, item: len(s.items) < s.capacity),
        Action(lambda s, item: prime(s.items) == s.items + (item,)),
        Modifies("items"),
    ]: ...

    def pop(self) -> Annotated[
        int,
        Requires(lambda s: len(s.items) > 0),
        Action(lambda s: prime(s.items) == s.items[1:]),
        Ensures(lambda s, result: result == old(s.items)[0]),
        Modifies("items"),
    ]: ...

class SimpleQueue(BoundedQueue):
    def push(self, item: int) -> None:
        self.items = self.items + (item,)

    def pop(self) -> int:
        val = self.items[0]
        self.items = self.items[1:]
        return val

m = Model(SimpleQueue, constants={"capacity": 2}, domains={"item": Domain.range(1, 2)})
"""
        runs = manyan.check_temporal(base)
        self.assertTrue(runs[0].ok, runs[0].run.output)

        # Buggy concrete pop violating inherited Protocol Ensures/Action is caught automatically.
        buggy = base.replace("val = self.items[0]\n        self.items = self.items[1:]", "val = self.items[-1]\n        self.items = self.items[:-1]")
        bad_runs = manyan.check_temporal(buggy)
        self.assertEqual(bad_runs[0].run.status, 12, bad_runs[0].run.output)
        assert bad_runs[0].run.result is not None
        self.assertIn("_Conform_pop", bad_runs[0].run.result.violated)

    def test_set_ops_comprehensions_view_action_constraint_assume_deadlock_and_action_inv(self) -> None:
        src = """from typing import Annotated
from temporal import Action, ActionInvariant, Assume, Constant, Init, Invariant, Model, State, prime

class SetsSpec:
    universe: Constant[frozenset[int]]
    a: State[frozenset[int]]
    b: State[frozenset[int]]
    m: State[dict[int, int]]

    non_empty: Annotated[bool, Assume(lambda s: len(s.universe) > 0)]
    init: Annotated[
        bool,
        Init(lambda s: s.a == {1} and s.b == {1, 2} and s.m == {k: k * 2 for k in s.universe if k > 0}),
    ]
    ok: Annotated[
        bool,
        Invariant(
            lambda s: (
                s.b >= s.a
                and s.b > s.a
                and s.a.issubset(s.b)
                and s.b.issuperset(s.a)
                and s.a.union({2}) == s.b
                and s.b.intersection(s.a) == s.a
                and s.b.difference(s.a) == {2}
                and {x + 1 for x in s.b if x > 1} == {3}
                and 1 in s.m
                and 0 not in s.m
            )
        ),
    ]
    monotone: Annotated[bool, ActionInvariant(lambda s: prime(s.b) >= s.b)]
    stutter: Annotated[bool, Action(lambda s: prime(s.a) == s.a and prime(s.b) == s.b)]

m = Model(
    SetsSpec,
    constants={"universe": frozenset({0, 1, 2})},
    view=lambda s: (s.a, s.b),
    action_constraint=lambda s: len(prime(s.b)) <= 2,
)
"""
        runs = manyan.check_temporal(src)
        self.assertTrue(runs[0].ok, runs[0].run.output)

        # Assumption violation -> exit 10
        bad_assume = src.replace("frozenset({0, 1, 2})", "frozenset()")
        r_assume = manyan.check_temporal(bad_assume)[0]
        self.assertEqual(r_assume.run.status, 10, r_assume.run.output)

        # ActionInvariant violation -> exit 13
        bad_ainv = """from typing import Annotated
from temporal import Action, ActionInvariant, Init, Model, State, prime

class Mono:
    x: State[int]
    init: Annotated[bool, Init(lambda s: s.x == 1)]
    non_decreasing: Annotated[bool, ActionInvariant(lambda s: prime(s.x) >= s.x)]
    dec: Annotated[bool, Action(lambda s: prime(s.x) == 0)]

m = Model(Mono)
"""
        r_ainv = manyan.check_temporal(bad_ainv)[0]
        self.assertEqual(r_ainv.run.status, 13, r_ainv.run.output)
        assert r_ainv.run.result is not None
        self.assertIn("non_decreasing", r_ainv.run.result.violated)

        # Deadlock detection -> exit 11 + human-readable CLI message
        deadlock_src = """from typing import Annotated
from temporal import Action, Init, Model, State, prime

class OneShot:
    x: State[int]
    init: Annotated[bool, Init(lambda s: s.x == 0)]
    step: Annotated[bool, Action(lambda s: s.x == 0 and prime(s.x) == 1)]

m = Model(OneShot)
"""
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "dl.py"
            p.write_text(deadlock_src, encoding="utf-8")
            res = _run_cli("check", str(p))
            self.assertEqual(res.returncode, 11, res.stdout + res.stderr)
            self.assertIn("deadlock (exit 11)", res.stdout)

    def test_all_remaining_temporal_primitives_end_to_end(self) -> None:
        src = """from typing import Annotated
from temporal import (
    Action, Domain, Fairness, Init, Invariant, Model, Property, State,
    StrongFairness, Unchanged, always, choose, enabled, eventually, iff, prime, weak_fairness,
)

class Primitives:
    x: State[int]
    flag: State[bool]
    mapping: State[dict[int, str]]

    init: Annotated[
        bool,
        Init(
            lambda s: (
                s.x == choose(Domain.range(0, 2), lambda v: v == 0)
                and s.flag is False
                and s.mapping == {0: "zero", 1: "one"}
            )
        ),
    ]
    check_iff_and_enabled: Annotated[
        bool,
        Invariant(
            lambda s: (
                s.x in Domain.range(0, 1)
                and iff(s.x == 0, s.mapping[s.x] == "zero")
                and (enabled(s.to_one) if s.x == 0 else enabled(s.to_zero))
            )
        ),
    ]
    infinitely_often_one: Annotated[bool, Property(lambda s: always(eventually(s.x == 1)))]
    eventually_flag: Annotated[bool, Property(lambda s: eventually(always(s.flag)))]
    fair_zero: Annotated[bool, Fairness(lambda s: weak_fairness(s.to_zero, on=s.x))]

    to_one: Annotated[
        bool,
        Action(lambda s: s.x == 0 and prime(s.x) == 1 and prime(s.flag) is True),
        Unchanged("mapping"),
        StrongFairness(),
    ]
    to_zero: Annotated[
        bool,
        Action(lambda s: s.x == 1 and prime(s.x) == 0),
        Unchanged("flag", "mapping"),
    ]

m = Model(Primitives)
"""
        runs = manyan.check_temporal(src)
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)

    def test_sequence_iteration_enumerate_dict_items_tuple_unpacking_and_local_collections(self) -> None:
        src = """from typing import Annotated
from temporal import Action, Domain, Init, Invariant, Model, Requires, State

class Collections:
    log: State[tuple[int, ...]]
    seen: State[frozenset[int]]
    pairs: State[frozenset[tuple[int, int]]]
    scores: State[dict[int, int]]

    init: Annotated[
        bool,
        Init(
            lambda s: (
                s.log == ()
                and s.seen == frozenset()
                and s.pairs == frozenset()
                and s.scores == {1: 10, 2: 20}
            )
        ),
    ]
    inv: Annotated[
        bool,
        Invariant(
            lambda s: (
                all(x in {1, 2} for x in s.log)
                and all(i < 2 and x > 0 for i, x in enumerate(s.log))
                and all(k in {1, 2} for k in s.scores)
                and all(v == k * 10 for k, v in s.scores.items())
                and all(a == b for a, b in s.pairs)
                and {x + 10 for x in s.log} <= {11, 12}
            )
        ),
    ]

    def record(self, item: int) -> Annotated[
        None,
        Requires(lambda s, item: len(s.log) < 2),
        Action(),
    ]:
        buf = list(self.log)
        buf.append(item)
        self.log = tuple(buf)
        st = set(self.seen)
        st.add(item)
        self.seen = frozenset(st)
        self.pairs = self.pairs | {(item, item)}

    def forget(self, item: int) -> Annotated[
        None,
        Requires(lambda s, item: item in s.seen),
        Action(),
    ]:
        st = set(self.seen)
        st.discard(item)
        self.seen = frozenset(st)

m = Model(Collections, domains={"item": Domain.values(1, 2)}, check_deadlock=False)
"""
        runs = manyan.check_temporal(src)
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].ok, runs[0].run.output)

    def test_module_constants_inline_model_values_pure_helpers_while_tuple_and_nondet_conformance(self) -> None:
        src = """from typing import Annotated
from temporal import Action, Ensures, Init, Invariant, Model, ModelValue, Pure, Requires, State, prime

LIMIT = 4

class Node(ModelValue):
    pass

PRIMARY = Node("n1")

def is_even(x: int) -> Pure[bool]:
    return x % 2 == 0

class Switch:
    leader: State[Node]
    val: State[int]

    init: Annotated[bool, Init(lambda s: s.leader == PRIMARY and s.val == 0)]
    ok: Annotated[
        bool,
        Invariant(lambda s: s.leader in {Node("n1"), Node("n2")} and 0 <= s.val <= LIMIT and is_even(s.val)),
    ]

    def reset(self) -> Annotated[
        None,
        Action(lambda s: prime(s.val) in {0, 2} and prime(s.leader) == Node("n1")),
    ]:
        self.val = 0
        self.leader = PRIMARY

    def step(self) -> Annotated[
        None,
        Requires(lambda s: s.val < LIMIT),
        Action(lambda s: prime(s.val) == s.val + 2),
    ]:
        self.val += 2

def fib(n: int) -> Annotated[
    Pure[int],
    Requires(lambda n: 0 <= n <= 5),
    Ensures(lambda n, result: result >= 0 and (n < 2 or result >= 1)),
]:
    a, b = 0, 1
    i = 0
    while i < n:
        a, b = b, a + b
        i += 1
    return a

m = Model(Switch)
"""
        # Default conformance mode: Switch.reset picks deterministic 0 (satisfies {0, 2}), plus fib passes!
        runs = manyan.check_temporal(src)
        self.assertEqual([r.name for r in runs], ["m", "fib"])
        for tr in runs:
            self.assertTrue(tr.ok, f"{tr.name}: {tr.run.output}")
        # Spec-only mode explores both 0 and 2 from nondeterministic reset (3 distinct states: 0, 2, 4).
        spec_runs = manyan.check_temporal(src, model="m", mode="spec-only")
        self.assertTrue(spec_runs[0].ok, spec_runs[0].run.output)
        assert spec_runs[0].run.result is not None
        self.assertEqual(spec_runs[0].run.result.distinct, 3)

    def test_pure_function_if_else_continuation_and_while_if_continuation(self) -> None:
        src = """from typing import Annotated
from temporal import Domain, Ensures, Model, Pure, Requires

def abs_val(x: int) -> Annotated[
    Pure[int],
    Ensures(lambda x, result: result >= 0 and (result == x or result == -x)),
]:
    y = 0
    if x >= 0:
        y = x
    else:
        y = -x
    return y

def gcd(a: int, b: int) -> Annotated[
    Pure[int],
    Requires(lambda a, b: a > 0 and b > 0),
    Ensures(lambda a, b, result: result > 0 and a % result == 0 and b % result == 0),
]:
    assert a > 0 and b > 0
    steps = 0
    while a != b:
        if a > b:
            a = a - b
        else:
            b = b - a
        steps += 1
    return a

gcd_model = Model(gcd, domains={"a": Domain.range(1, 6), "b": Domain.range(1, 6)})
"""
        runs = manyan.check_temporal(src)
        self.assertEqual([r.name for r in runs], ["gcd_model", "abs_val"])
        for tr in runs:
            self.assertTrue(tr.ok, f"{tr.name}: {tr.run.output}")

    def test_list_and_sum_comprehensions(self) -> None:
        src = """from typing import Annotated
from temporal import Action, Init, Invariant, Model, State, prime

class Vec:
    xs: State[tuple[int, ...]]
    init: Annotated[bool, Init(lambda s: s.xs == tuple(i for i in range(1, 4)))]
    ok: Annotated[
        bool,
        Invariant(
            lambda s: (
                [x * 2 for x in s.xs] == (2, 4, 6)
                and sum(x * x for x in s.xs) == 14
            )
        ),
    ]
    stutter: Annotated[bool, Action(lambda s: prime(s.xs) == s.xs)]

m = Model(Vec)
"""
        runs = manyan.check_temporal(src)
        self.assertTrue(runs[0].ok, runs[0].run.output)


class TestTemporalCLI(unittest.TestCase):
    def test_cli_check_pass_and_fail(self) -> None:
        ok = _run_cli("check", str(EXAMPLES / "semaphore.py"))
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
        self.assertIn("PASS", ok.stdout)

        # Direct .py shortcut without 'check' subcommand
        direct = _run_cli(str(EXAMPLES / "mutex.py"))
        self.assertEqual(direct.returncode, 0, direct.stdout + direct.stderr)
        self.assertIn("PASS", direct.stdout)

        # Invariant violation returns exit status 12 with trace
        fail = _run_cli("check", "--model", "impl_model", str(EXAMPLES / "die_hard.py"))
        self.assertEqual(fail.returncode, 12, fail.stdout + fail.stderr)
        self.assertIn("FAIL", fail.stdout)
        self.assertIn("not_solved", fail.stdout)
        self.assertIn("big = 4", fail.stdout)

    def test_cli_emit(self) -> None:
        res = _run_cli("emit", str(EXAMPLES / "semaphore.py"))
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn("---- MODULE Semaphore_semaphore_model ----", res.stdout)
        self.assertIn("SPECIFICATION Spec", res.stdout)

    def test_cli_non_py_still_passes_through_to_manyan_binary(self) -> None:
        res = _run_cli("-version")
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertTrue(res.stdout.startswith("manyan version "))

    def test_cli_empty_python_file_reports_error(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "empty.py"
            p.write_text("x = 1\n", encoding="utf-8")
            res = _run_cli("check", str(p))
            self.assertEqual(res.returncode, 1)
            self.assertIn("no Temporal specifications found", res.stderr)

    def test_cli_directory_check_skips_plain_python_files(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "helper.py").write_text("VALUE = 42\n", encoding="utf-8")
            (Path(d) / "sem.py").write_text((EXAMPLES / "semaphore.py").read_text(encoding="utf-8"), encoding="utf-8")
            res = _run_cli("check", d)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn("PASS", res.stdout)
            self.assertIn("Checked 1 Temporal model(s): 1 passed.", res.stdout)

    def test_cli_symbolic_and_workers(self) -> None:
        # Symbolic SMT checking finds the 7-state Die Hard solution directly from Python
        sym = _run_cli("check", "--symbolic", "--length", "7", "--model", "impl_model", str(EXAMPLES / "die_hard.py"))
        self.assertEqual(sym.returncode, 12, sym.stdout + sym.stderr)
        self.assertIn("not_solved", sym.stdout)
        self.assertIn("big = 4", sym.stdout)

        # Symbolic SMT checking proves Semaphore safe up to length 6
        sym_ok = _run_cli("check", "--symbolic", "--length", "6", str(EXAMPLES / "semaphore.py"))
        self.assertEqual(sym_ok.returncode, 0, sym_ok.stdout + sym_ok.stderr)
        self.assertIn("PASS", sym_ok.stdout)

        # Multi-worker checking on BankAccount matches exact distinct state count
        w2 = _run_cli("check", "--workers", "2", str(EXAMPLES / "bank_account.py"))
        self.assertEqual(w2.returncode, 0, w2.stdout + w2.stderr)
        self.assertIn("884 distinct states", w2.stdout)


if __name__ == "__main__":
    unittest.main()
