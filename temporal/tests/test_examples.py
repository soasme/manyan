"""End-to-end tests verifying all Temporal examples execute, inspect, and remain passive."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path
from types import ModuleType

from temporal import Role, get_contract, get_spec

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
        spec_info = get_spec(mod.DieHardSpec)
        self.assertEqual(set(spec_info.state), {"small", "big"})
        self.assertEqual(set(spec_info.inits), {"init"})
        self.assertEqual(len(spec_info.actions), 6)
        self.assertEqual(set(spec_info.invariants), {"type_ok", "not_solved"})

        # Execute the real DieHard solution in ordinary Python!
        jugs = mod.DieHard()
        self.assertTrue(jugs.init())
        self.assertTrue(jugs.type_ok())
        self.assertTrue(jugs.not_solved())
        jugs.fill_big()
        jugs.pour_big_to_small()
        jugs.empty_small()
        jugs.pour_big_to_small()
        jugs.fill_big()
        jugs.pour_big_to_small()
        self.assertEqual((jugs.small, jugs.big), (3, 4))
        self.assertTrue(jugs.type_ok())
        self.assertFalse(jugs.not_solved())

    def test_bank_account(self) -> None:
        mod = _load_example("bank_account")
        spec_info = get_spec(mod.BankAccount)
        self.assertEqual(set(spec_info.constants), {"owner", "credit_limit"})
        self.assertEqual(set(spec_info.state), {"balance"})
        self.assertEqual(set(spec_info.ghost), {"ledger"})
        self.assertEqual(set(spec_info.assumptions), {"valid_owner"})
        self.assertEqual(set(spec_info.invariants), {"within_limit", "ledger_matches_balance"})
        self.assertEqual(set(spec_info.action_invariants), {"ledger_append_only"})
        self.assertEqual(set(spec_info.actions), {"deposit", "withdraw"})
        self.assertEqual(set(spec_info.pure), {"available"})

        acct = mod.BankAccount(owner="alice", credit_limit=50)
        self.assertTrue(acct.valid_owner())
        acct.deposit(100)
        self.assertEqual(acct.balance, 100)
        self.assertEqual(acct.available, 150)
        out = acct.withdraw(120)
        self.assertEqual(out, 120)
        self.assertEqual(acct.balance, -20)
        self.assertTrue(acct.within_limit())

    def test_bounded_queue_and_ring_buffer(self) -> None:
        mod = _load_example("bounded_queue")
        proto_info = get_spec(mod.BoundedQueue)
        self.assertEqual(set(proto_info.constants), {"capacity"})
        self.assertEqual(set(proto_info.state), {"items"})
        self.assertEqual(set(proto_info.actions), {"push", "pop"})
        self.assertEqual(set(proto_info.properties), {"eventually_drained"})

        rb_info = get_spec(mod.RingBuffer)
        self.assertEqual(set(rb_info.state), {"_buf", "_head", "_size"})
        self.assertIn("refines_queue", rb_info.refinements)

        rb = mod.RingBuffer(capacity=3)
        self.assertTrue(rb.init())
        self.assertTrue(rb.shape_ok())
        rb.push("a")
        rb.push("b")
        self.assertEqual(rb.pop(), "a")
        rb.push("c")
        rb.push("d")
        self.assertEqual(rb.size, 3)
        self.assertEqual(rb.refines_queue().mapping["items"], ("b", "c", "d"))
        self.assertEqual([rb.pop(), rb.pop(), rb.pop()], ["b", "c", "d"])
        self.assertTrue(rb.shape_ok())

    def test_mutex(self) -> None:
        mod = _load_example("mutex")
        info = get_spec(mod.Mutex)
        self.assertEqual(set(info.constants), {"procs"})
        self.assertEqual(set(info.state), {"holder", "waiting"})
        self.assertEqual(set(info.assumptions), {"non_empty_procs"})
        self.assertEqual(set(info.actions), {"request", "acquire", "release"})
        self.assertEqual(set(info.fairness), {"fair"})
        self.assertEqual(set(info.invariants), {"type_ok", "never_deadlocks"})
        self.assertEqual(set(info.properties), {"starvation_free"})
        self.assertEqual(mod.mutex_model.symmetries, (mod.PROCS,))

    def test_two_phase_commit(self) -> None:
        mod = _load_example("two_phase_commit")
        info = get_spec(mod.TwoPhaseCommit)
        self.assertEqual(set(info.constants), {"rms"})
        self.assertEqual(set(info.state), {"rm_state", "tm_state", "tm_prepared"})
        self.assertEqual(len(info.actions), 6)
        self.assertEqual(set(info.invariants), {"consistent", "commit_requires_all_prepared"})
        self.assertEqual(set(info.fairness), {"fair"})
        self.assertEqual(set(info.properties), {"decision_propagates"})
        self.assertFalse(mod.two_phase_model.check_deadlock)
        self.assertEqual(mod.two_phase_model.symmetries, (mod.RMS,))

    def test_pure_contracts(self) -> None:
        mod = _load_example("contracts")
        for fn_name in ("integer_sqrt", "binary_search", "clamp"):
            c = get_contract(getattr(mod, fn_name))
            self.assertIs(c.role, Role.PURE)
            self.assertEqual(len(c.ensures), 1)

        self.assertEqual([mod.integer_sqrt(n) for n in range(10)], [0, 1, 1, 1, 2, 2, 2, 2, 2, 3])
        self.assertEqual(mod.binary_search((1, 3, 5, 7, 9), 7), 3)
        self.assertIsNone(mod.binary_search((1, 3, 5, 7, 9), 4))
        self.assertEqual(mod.clamp(-5, 0, 10), 0)
        self.assertEqual(mod.clamp(5, 0, 10), 5)
        self.assertEqual(mod.clamp(50, 0, 10), 10)


if __name__ == "__main__":
    unittest.main()
