"""End-to-end tests for checking Python Temporal specifications via `manyan`."""
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))
import manyan  # noqa: E402

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


if __name__ == "__main__":
    unittest.main()
