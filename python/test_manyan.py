"""manyan.run's result: what the check found, as values. `make test-python`
runs it on ./manyan, or on the executable MANYAN names."""
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))
import manyan  # noqa: E402
from manyan import Function, Printed  # noqa: E402

manyan.find_manyan_bin = lambda: os.environ.get("MANYAN", str(ROOT / "manyan"))


def check(args, files):
    with tempfile.TemporaryDirectory() as d:
        for name, text in files.items():
            Path(d, name).write_text(text)
        return manyan.run(args, cwd=d)


def spec(name, body, cfg):
    return {f"{name}.tla": f"---- MODULE {name} ----\n{body}\n====\n", f"{name}.cfg": cfg}


def cycle(prop, fair):
    fairness = " /\\ WF_x(Next)" if fair else ""
    return spec("L", "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\n"
                f"Spec == Init /\\ [][Next]_x{fairness}\nP == {prop}", "SPECIFICATION Spec\nPROPERTY P\n")


class TestResult(unittest.TestCase):
    def test_invariant(self):
        files = {f: (ROOT / "examples" / f).read_text() for f in ("DieHard.tla", "DieHard.cfg")}
        run = check(["DieHard"], files)
        r = run.result
        self.assertEqual(run.status, 12)
        self.assertIn("Invariant NotSolved is violated", run.output)
        self.assertEqual(r.violated, ["NotSolved"])
        self.assertEqual(len(r.states), 7)
        self.assertEqual(r.states[0], {"small": 0, "big": 0})
        self.assertEqual(r.states[-1], {"small": 3, "big": 4})
        self.assertEqual([a["name"] for a in r.actions], ["Init"] + ["Next"] * 6)
        self.assertEqual(r.actions[1]["location"],
                         {"beginLine": 9, "beginColumn": 12, "endLine": 9, "endColumn": 37, "module": "DieHard"})
        self.assertEqual((r.loop, r.generated, r.distinct, r.left, r.depth), (0, 73, 14, 1, 7))

    def test_values(self):
        r = check(["V"], spec("V", """EXTENDS Naturals
CONSTANT M
VARIABLE t, r, f, s, m, g
Init == t = <<1, "a", TRUE>> /\\ r = [a |-> {1, 2}, tla |-> "M"] /\\ f = [i \\in {0, 1} |-> i = 0] /\\ m = M
  /\\ s = {[a |-> 1], [a |-> 2]} /\\ g = [k \\in {"a b", "#tla"} |-> 0]
Next == UNCHANGED <<t, r, f, s, m, g>>
Inv == m # M""", "CONSTANT M = M\nINIT Init\nNEXT Next\nINVARIANT Inv\n")).result
        state = r.states[0]
        self.assertEqual(state, {"t": (1, "a", True), "r": {"a": frozenset({1, 2}), "tla": "M"}, "f": {0: True, 1: False},
                                 "s": frozenset({Function(a=1), Function(a=2)}), "m": "M", "g": {"a b": 0, "#tla": 0}})
        self.assertIsInstance(state["m"], Printed)
        self.assertNotIsInstance(state["r"]["tla"], Printed)
        self.assertIsInstance(state["f"], Function)

    def test_lasso(self):
        run = check(["L"], cycle("<>(x = 5)", True))
        r = run.result
        self.assertEqual(run.status, 13)
        self.assertEqual((r.states, r.loop, r.violated), ([{"x": 0}, {"x": 1}, {"x": 2}], 1, ["P"]))
        self.assertEqual([a["name"] for a in r.actions], ["Init", "Next", "Next", "Next"])

    def test_stuttering(self):
        r = check(["L"], cycle("<>(x = 1)", False)).result
        self.assertEqual((r.states, r.loop, len(r.actions)), ([{"x": 0}], 1, 2))

    def test_no_error(self):
        run = check(["L"], cycle("[](x < 3)", True))
        r = run.result
        self.assertEqual(run.status, 0)
        self.assertEqual((r.states, r.actions, r.loop, r.violated), ([], [], 0, []))
        self.assertEqual((r.generated, r.distinct, r.left, r.depth), (4, 3, 0, 3))

    def test_simulation(self):
        r = check(["-simulate", "-seed", "1", "S"], spec("S", "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\n"
                  "Next == x' = x + 1\nInv == x < 2", "INIT Init\nNEXT Next\nINVARIANT Inv\n")).result
        self.assertEqual((r.states, r.generated, r.distinct), ([{"x": 0}, {"x": 1}, {"x": 2}], 3, None))

    def test_parse_error(self):
        run = check(["P"], spec("P", "VARIABLE", "INIT Init\n"))
        self.assertEqual(run.status, 150)
        self.assertEqual((run.result.states, run.result.generated), ([], None))

    def test_usage_error(self):
        run = check(["-workers"], {})
        self.assertIsNone(run.result)

    def test_version(self):
        run = check(["-version"], {})
        self.assertIsNone(run.result)
        self.assertTrue(run.output.startswith("manyan version "))


if __name__ == "__main__":
    unittest.main()
