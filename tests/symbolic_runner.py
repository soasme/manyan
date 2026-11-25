"""Run the symbolic checking tests (tests/symbolic) on Manyan, with Apalache as the oracle.

usage: symbolic_runner.py MANYAN [--oracle APALACHE] [--bless] [--only SUBSTRING] [--strict]

A test is NAME.tla, a module and then its model configuration, as in
tests/spec; a line `\\* options: -length N -deadlock -cinit C` gives the
length (10 by default), turns deadlock checking off, names the
operator that chooses the constants and how many errors to find (the
configuration's VIEW tells them apart). NAME.out is the outcome
Apalache gives: NoError, Error with the violated invariant or property,
or Deadlock, then the number of states in the (first) counterexample
and, if more than one is found, how many; then the exit status; or Refused, where Apalache stops without a verdict (exit
status 255, 75 or 120) and Manyan stops with an error, its own (TLC's)
exit status, not a bug or a crash. For a property the counterexample is a lasso, whose length
is not compared: Apalache closes a loop only where its tableau's own
variables repeat too, so it may find only a longer one than Manyan.
The traces themselves are the solver's choice and are not compared;
Manyan replays each of its own through its evaluator. But where a test
has NAME.itf.json, Manyan's -run-dir must write it, the last
counterexample in ITF, as violation.itf.json.

With --oracle, Apalache (its apalache-mc) must give NAME.out too, which
validates the test; --bless writes NAME.out from it. Each run is killed
past --memory MB resident (1000, or 3000 with Apalache's JVM), and only
as many run at once as keep to half the machine's memory.
"""
import argparse
import re
import shlex
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from spec_runner import ROOT, guarded, stage, workers

TESTS = ROOT / "tests/symbolic"


def options(path):
    found = re.search(r"^\\\* options: (.*)$", path.read_text(), flags=re.M)
    words = shlex.split(found.group(1)) if found else []
    length = words[words.index("-length") + 1] if "-length" in words else "10"
    cinit = words[words.index("-cinit") + 1] if "-cinit" in words else None
    errors = words[words.index("-max-error") + 1] if "-max-error" in words else None
    return length, "-deadlock" in words, cinit, errors


def named(config, keyword):
    """The names the configuration's statements of keyword (INVARIANT, PROPERT) give, in order."""
    names = []
    for m in re.finditer(rf"^\s*{keyword}\w*\b(.*?)(?=^\s*[A-Z_]+\b|\Z)", config, flags=re.M | re.S):
        names += m.group(1).split()
    return names


def errors(n):
    return f" errors {n}" if n > 1 else ""


def manyan_outcome(output, code):
    invariant = r"^Error: Invariant (\S+) is violated(\.| by the initial state:)$"
    first = re.split(invariant, output, flags=re.M)[::3]
    states = len(re.findall(r"^State \d+: ", first[1] if len(first) > 2 else output, flags=re.M))
    violated = re.search(invariant, output, flags=re.M)
    if violated:
        states = states if violated.group(2) == "." else 1   # TLC prints the initial state unnumbered
        return f"Error {violated.group(1)} {states}{errors(len(first) - 1)}\nexit {code}\n"
    violated = re.search(r"^Error: Temporal property (\S+) was violated\.$", output, flags=re.M)
    if violated:
        return f"Error {violated.group(1)}\nexit {code}\n"
    if re.search(r"^Error: Deadlock reached\.$", output, flags=re.M):
        return f"Deadlock {states}\nexit {code}\n"
    if "No error has been found in behaviors" in output:
        return f"NoError\nexit {code}\n"
    if "No error has been found. No " in output:
        return f"ExecutionsTooShort\nexit {code}\n"
    error = re.search(r"^Error: (.*)$", output, flags=re.M)
    if code > 0 and "This is a bug" not in output:
        return "Refused\n"
    return f"Failure {error.group(1) if error else output.strip()[-200:]}\nexit {code}\n"


def apalache_outcome(output, code, directory, config):
    outcome = re.search(r"The outcome is: (\w+)", output)
    if code in (75, 120, 255):
        return "Refused\n"
    if not outcome:
        error = re.search(r"^.*(?:error|Error|ERROR).*$", output, flags=re.M)
        return f"Failure {error.group(0).strip() if error else 'no outcome'}\nexit {code}\n"
    outcome = outcome.group(1)
    if outcome in ("NoError", "ExecutionsTooShort"):
        return f"{outcome}\nexit {code}\n"
    traces = sorted(directory.rglob("violation1.tla")) or sorted(directory.rglob("violation*.tla"))
    states = len(re.findall(r"^State\d+ ==", traces[0].read_text(), flags=re.M)) if traces else 0
    found = re.search(r"^Found (\d+) error\(s\)", output, flags=re.M)
    if outcome == "Deadlock":   # Apalache exits 12 for it, TLC (and Manyan) 11
        return f"Deadlock {states}\nexit 11\n"
    # Apalache numbers the invariants it checks, a labelled conjunction's conjuncts apart.
    which = re.search(r"State \d+: (?:state|action) invariant (\d+) violated", output)
    names, properties = named(config, "INVARIANT"), named(config, "PROPERT")
    if properties and not names:   # its tableau's invariant; Apalache exits 12 for it, TLC (and Manyan) 13
        return f"{outcome} {properties[0] if len(properties) == 1 else '?'}\nexit 13\n"
    if len(names) == 1:
        name = names[0]
    else:
        name = names[int(which.group(1))] if which and int(which.group(1)) < len(names) else "?"
    return f"{outcome} {name} {states}{errors(int(found.group(1)) if found else 1)}\nexit {code}\n"


def run(command, path, oracle, memory):
    length, no_deadlock, cinit, max_error = options(path)
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp).resolve()
        stage(path, directory)
        cfg = path.stem + ".cfg"
        if oracle:
            args = command + ["check", f"--config={cfg}", f"--length={length}", f"--out-dir={directory}/out"]
            args += ["--no-deadlock"] if no_deadlock else []
            args += [f"--cinit={cinit}"] if cinit else []
            args += [f"--max-error={max_error}"] if max_error else []
            args += [f"--view={v}" for v in named((directory / cfg).read_text(), "VIEW")]
            args += [path.name]
        else:
            args = command + ["-symbolic", "-length", length] + (["-deadlock"] if no_deadlock else [])
            args += ["-cinit", cinit] if cinit else []
            args += ["-max-error", max_error] if max_error else []
            args += ["-run-dir", f"{directory}/run"] if path.with_suffix(".itf.json").exists() else []
            args += ["-config", cfg, path.stem]
        _, output, code, killed = guarded(args, directory, 600, memory, b"")
        if killed:
            return f"{killed}\n", output, None
        if oracle:
            return apalache_outcome(output, code, directory, (directory / cfg).read_text()), output, None
        itf = directory / "run/violation.itf.json"
        return manyan_outcome(output, code), output, itf.read_text() if itf.exists() else None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("engine")
    parser.add_argument("--oracle")
    parser.add_argument("--bless", action="store_true")
    parser.add_argument("--only", default="")
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--memory", type=int)
    args = parser.parse_args()
    memory = args.memory or (3000 if args.oracle else 1000)
    engine = shlex.split(args.engine)
    if "/" in engine[0]:
        engine[0] = str(Path(engine[0]).resolve())
    oracle = shlex.split(args.oracle) if args.oracle else None
    if oracle and "/" in oracle[0]:
        oracle[0] = str(Path(oracle[0]).resolve())
    tests = sorted(p for p in TESTS.rglob("*.tla") if ".files" not in p.parent.name and args.only in str(p.relative_to(TESTS)))

    def check(path):
        expected_path = path.with_suffix(".out")
        notes = []
        if args.oracle:
            reference, log, _ = run(oracle, path, True, memory)
            if args.bless:
                expected_path.write_text(reference)
            elif not expected_path.exists() or reference != expected_path.read_text():
                notes.append("oracle disagrees with " + expected_path.name + ": " + reference.replace("\n", " "))
        if not expected_path.exists():
            return path, False, ["no " + expected_path.name], ""
        actual, output, itf = run(engine, path, False, memory)
        if actual != expected_path.read_text():
            notes.append("outcome differs: " + actual.replace("\n", " "))
        itf_path = path.with_suffix(".itf.json")
        if itf_path.exists() and itf != itf_path.read_text():
            notes.append("ITF differs from " + itf_path.name)
        return path, not notes, notes, output

    failed = 0
    with ThreadPoolExecutor(max_workers=workers(memory)) as pool:
        for path, ok, notes, output in pool.map(check, tests):
            if not ok:
                failed += 1
                print("FAIL", path.relative_to(ROOT), "-", "; ".join(notes))
                if args.verbose:
                    print(output)
    print(f"{'symbolic':24} {len(tests) - failed:4}/{len(tests)}")
    return 1 if failed and args.strict else 0


if __name__ == "__main__":
    sys.exit(main())
