"""End-to-end tests verifying all Temporal examples import, run, and expose PEP 593 annotations."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path
from types import ModuleType
from typing import Annotated, get_args, get_origin, get_type_hints

from temporal import Action, Fairness, Init, Invariant, Property, Role

EXAMPLES_DIR = Path(__file__).resolve().parent.parent / "examples"


def _load_example(name: str) -> ModuleType:
    path = EXAMPLES_DIR / f"{name}.py"
    spec = importlib.util.spec_from_file_location(f"temporal_example_{name}", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class TestExamples(unittest.TestCase):
    def test_die_hard(self) -> None:
        mod = _load_example("die_hard")
        hints = get_type_hints(mod.DieHardSpec, include_extras=True)
        self.assertIs(get_args(hints["small"])[1], Role.STATE)
        self.assertIsInstance(get_args(hints["init"])[1], Init)
        self.assertIsInstance(get_args(hints["fill_small"])[1], Action)
        self.assertIsInstance(get_args(hints["not_solved"])[1], Invariant)

        jugs = mod.DieHard()
        jugs.fill_big()
        jugs.pour_big_to_small()
        jugs.empty_small()
        jugs.pour_big_to_small()
        jugs.fill_big()
        jugs.pour_big_to_small()
        self.assertEqual((jugs.small, jugs.big), (3, 4))

    def test_bank_account(self) -> None:
        mod = _load_example("bank_account")
        acct = mod.BankAccount(owner="alice", credit_limit=50)
        acct.deposit(100)
        self.assertEqual(acct.balance, 100)
        self.assertEqual(acct.available, 150)
        self.assertEqual(acct.withdraw(120), 120)
        self.assertEqual(acct.balance, -20)

    def test_bounded_queue_and_ring_buffer(self) -> None:
        mod = _load_example("bounded_queue")
        hints = get_type_hints(mod.BoundedQueue, include_extras=True)
        self.assertIsInstance(get_args(hints["bounded"])[1], Invariant)
        self.assertIsInstance(get_args(hints["eventually_makes_space"])[1], Property)

        rb = mod.RingBuffer(capacity=3)
        rb.push("a")
        rb.push("b")
        self.assertEqual(rb.pop(), "a")
        rb.push("c")
        rb.push("d")
        self.assertEqual(rb.size, 3)
        self.assertEqual(rb.refines_queue().mapping["items"], ("b", "c", "d"))
        self.assertEqual([rb.pop(), rb.pop(), rb.pop()], ["b", "c", "d"])

    def test_mutex(self) -> None:
        mod = _load_example("mutex")
        hints = get_type_hints(mod.Mutex, include_extras=True)
        self.assertIs(get_args(hints["procs"])[1], Role.CONSTANT)
        self.assertIsInstance(get_args(hints["fair"])[1], Fairness)
        self.assertIsInstance(get_args(hints["starvation_free"])[1], Property)
        self.assertIs(mod.mutex_model.spec, mod.Mutex)

    def test_two_phase_commit(self) -> None:
        mod = _load_example("two_phase_commit")
        hints = get_type_hints(mod.TwoPhaseCommit, include_extras=True)
        self.assertIsInstance(get_args(hints["consistent"])[1], Invariant)
        self.assertIsInstance(get_args(hints["decision_propagates"])[1], Property)
        self.assertFalse(mod.two_phase_model.check_deadlock)

    def test_semaphore(self) -> None:
        mod = _load_example("semaphore")
        hints = get_type_hints(mod.Semaphore, include_extras=True)
        self.assertIs(get_args(hints["capacity"])[1], Role.CONSTANT)
        self.assertIsInstance(get_args(hints["bounded"])[1], Invariant)
        self.assertIsInstance(get_args(hints["progress"])[1], Property)

        sem = mod.Semaphore(capacity=2)
        self.assertTrue(sem.acquire())
        self.assertEqual(sem.available, 1)
        sem.release()
        self.assertEqual(sem.available, 2)

    def test_pure_contracts(self) -> None:
        mod = _load_example("contracts")
        for fn_name in ("integer_sqrt", "binary_search", "clamp"):
            ret = get_type_hints(getattr(mod, fn_name), include_extras=True)["return"]
            self.assertIs(get_origin(ret), Annotated)
            self.assertIn(Role.PURE, get_args(ret))

        self.assertEqual(
            [mod.integer_sqrt(n) for n in range(10)], [0, 1, 1, 1, 2, 2, 2, 2, 2, 3]
        )
        self.assertEqual(mod.binary_search((1, 3, 5, 7, 9), 7), 3)
        self.assertIsNone(mod.binary_search((1, 3, 5, 7, 9), 4))
        self.assertEqual(mod.clamp(-5, 0, 10), 0)
        self.assertEqual(mod.clamp(5, 0, 10), 5)
        self.assertEqual(mod.clamp(50, 0, 10), 10)


if __name__ == "__main__":
    unittest.main()
