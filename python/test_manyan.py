"""manyan.run's result: what the check found, as values; and manyan.check's,
the same in this process. `make test-python` runs them on ./manyan and on
the library MANYAN_LIB names, or on the executable MANYAN names."""
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
manyan.find_manyan_lib = lambda: os.environ["MANYAN_LIB"]


def check(args, files, **options):
    """manyan.run(args), which, for a spec, manyan.check(spec, **options) gives too."""
    with tempfile.TemporaryDirectory() as d:
        for name, text in files.items():
            Path(d, name).write_text(text)
        run = manyan.run(args, cwd=d)
        if args and not args[-1].startswith("-") and "MANYAN_LIB" in os.environ:
            here = os.getcwd()
            os.chdir(d)
            try:
                assert manyan.check(args[-1], **options) == run, args
            finally:
                os.chdir(here)
        return run


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
                  "Next == x' = x + 1\nInv == x < 2", "INIT Init\nNEXT Next\nINVARIANT Inv\n"),
                  simulate=True, seed=1).result
        self.assertEqual((r.states, r.generated, r.distinct), ([{"x": 0}, {"x": 1}, {"x": 2}], 3, None))

    def test_parse_error(self):
        run = check(["P"], spec("P", "VARIABLE", "INIT Init\n"))
        self.assertEqual(run.status, 150)
        self.assertEqual((run.result.states, run.result.generated), ([], None))

    def test_options(self):
        files = {"D.tla": (ROOT / "examples/DieHard.tla").read_text().replace("MODULE DieHard", "MODULE D"),
                 "M.cfg": "INIT Init\nNEXT Next\n"}
        r = check(["-workers", "4", "-deadlock", "-config", "M.cfg", "-Dtlc2.tool.impl.Tool.cdot=true", "D"], files,
                  workers=4, check_deadlock=False, config="M.cfg", properties=["tlc2.tool.impl.Tool.cdot=true"]).result
        self.assertEqual((r.violated, r.distinct), ([], 16))
        with self.assertRaises(TypeError):
            manyan.check("DieHard", deadlock=False)

    def test_usage_error(self):
        run = check(["-workers"], {})
        self.assertIsNone(run.result)

    def test_version(self):
        run = check(["-version"], {})
        self.assertIsNone(run.result)
        self.assertTrue(run.output.startswith("manyan version "))

    def test_lint(self):
        ok = check(["-lint", "M"], {"M.tla": "---- MODULE M ----\nEXTENDS Naturals\nA == 1 + 2\n====\n"}, lint=1)
        self.assertEqual(ok.status, 0)
        bad = check(["-lint", "M"], {"M.tla": "---- MODULE M ----\nA == Missing\n====\n"}, lint=1)
        self.assertEqual(bad.status, 150)
        self.assertIn("Unknown operator", bad.output)

    def test_fmt(self):
        run = check(["-fmt", "M"], {"M.tla": "-------- MODULE M --------\nVARIABLE  x,y\nInit==x=0/\\y=1\n========\n"}, fmt=1)
        self.assertEqual(run.status, 0)
        self.assertEqual(run.output, "---- MODULE M ----\nVARIABLES x, y\nInit == x = 0 /\\ y = 1\n====\n")

    def test_invalid_c_options(self):
        if "MANYAN_LIB" not in os.environ:
            return
        with tempfile.TemporaryDirectory() as d:
            Path(d, "M.tla").write_text("---- MODULE M ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====\n")
            Path(d, "M.cfg").write_text("INIT Init\nNEXT Next\n")
            here = os.getcwd()
            os.chdir(d)
            try:
                self.assertEqual(manyan.check("M", properties=["no_equals"]).status, 255)
                self.assertEqual(manyan.check("M", postconditions=["no_bang"]).status, 255)
                self.assertEqual(manyan.check("M", postconditions=["M!"]).status, 255)
            finally:
                os.chdir(here)

    def test_tlcset_encode_error_no_crash(self):
        run = check(["R"], spec("R", """EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == AssertError("x", TLCSet(1, Nat)) = FALSE /\\ x = TLCGet(1)
Next == x' = x""", "INIT Init\nNEXT Next\n"))
        self.assertEqual(run.status, 75)
        self.assertIn("TLCGet(1) was undefined", run.output)

    def test_json_safety_cases(self):
        # Regression for #20: deep nesting, NUL bytes, and lone high surrogate in JsonDeserialize
        deep = "[" * 5000 + "1" + "]" * 5000
        run = check(["J"], {**spec("J", 'EXTENDS Json\nVARIABLE x\nInit == x = JsonDeserialize("d.json")\nNext == x\' = x',
                                   "INIT Init\nNEXT Next\n"), "d.json": deep})
        self.assertEqual(run.status, 75)
        run2 = check(["J2"], {**spec("J2", 'EXTENDS Json\nVARIABLE x\nInit == x = JsonDeserialize("s.json")\nNext == x\' = x\nInv == x # "\\u2441"',
                                     "INIT Init\nNEXT Next\nINVARIANT Inv\n"), "s.json": '"\\uD800\\u0041"'})
        self.assertEqual(run2.status, 0)
        run3 = check(["J3"], {**spec("J3", 'EXTENDS Json\nVARIABLE x\nInit == x = JsonDeserialize("n.json")\nNext == x\' = x',
                                     "INIT Init\nNEXT Next\n"), "n.json": "\x001"})
        self.assertEqual(run3.status, 75)
        run4 = check(["CS"], {**spec("CS", 'EXTENDS Statistics\nVARIABLE x\nInit == x = ChiSquare(<<1, 1>>, <<1, 1>>, "1e60")\nNext == x\' = x',
                                     "INIT Init\nNEXT Next\n"),
                              "Statistics.tla": (ROOT / "tests/spec/stdlib/chi_square.files/Statistics.tla").read_text()})
        self.assertEqual(run4.status, 75)
        self.assertIn("out of bounds significance level", run4.output)


if __name__ == "__main__":
    unittest.main()
