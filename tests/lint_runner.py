"""Run the lint tests (tests/lint) on Manyan, with SANY as the oracle.

usage: lint_runner.py MANYAN [--oracle SANY] [--bless] [--only SUBSTRING] [--strict]

A test is NAME.tla, a module, with the modules it uses in NAME.files.
NAME.out is the outcome `tla2sany.SANY -error-codes` gives: normalized warnings
and lint messages (if any), followed by `OK` or `PARSE ERROR` or `SEMANTIC ERROR`.
Manyan's `-lint` must give the same outcome (exit 0 on OK, 150 on error) and the
same warnings and record-field lint messages.

With --oracle, SANY must give NAME.out too; --bless writes NAME.out from it.
"""
import argparse
import re
import shlex
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from spec_runner import ROOT, guarded, stage, workers

TESTS = ROOT / "tests/lint"

NOISE = re.compile(
    r"^(\*\*\*\*\*\* SANY2|manyan version|Parsing file|Semantic processing|Linting of module|GuardMalloc\[|Sysctl \(debug\.toggle_address_reuse\))")


def outcome(output, code, oracle):
    if code != 0:
        if oracle:
            if "***Parse Error***" in output or "Fatal errors while parsing" in output:
                return "PARSE ERROR\n"
            return "SEMANTIC ERROR\n"
        return "SEMANTIC ERROR\n" if "Semantic errors:" in output else "PARSE ERROR\n"
    lines = []
    for line in output.splitlines():
        if NOISE.match(line):
            continue
        if line.strip() == "" and (not lines or lines[-1] == ""):
            continue
        lines.append(line.rstrip())
    while lines and lines[-1] == "":
        lines.pop()
    return ("\n".join(lines) + "\n" if lines else "") + "OK\n"


def run(command, path, oracle, memory):
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp).resolve()
        stage(path, directory)
        if oracle:
            args = command + ["-error-codes", path.name]
        else:
            args = command + ["-lint", path.stem]
        _, output, code, killed = guarded(args, directory, 300, memory, b"")
        if killed:
            return f"{killed}\n", output
        if not oracle and code not in (0, 150):
            return f"unexpected exit {code}\n", output
        return outcome(output, code, oracle), output


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
    memory = args.memory or (3000 if args.oracle else 500)
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
        if oracle:
            reference, _ = run(oracle, path, True, memory)
            if args.bless:
                expected_path.write_text(reference)
            elif not expected_path.exists() or reference != expected_path.read_text():
                notes.append("oracle disagrees with " + expected_path.name + ": " + reference.replace("\n", " "))
        if not expected_path.exists():
            return path, False, ["no " + expected_path.name], ""
        actual, output = run(engine, path, False, memory)
        if actual != expected_path.read_text():
            notes.append("outcome differs: " + actual.replace("\n", " "))
        return path, not notes, notes, output

    failed = 0
    with ThreadPoolExecutor(max_workers=1 if args.oracle else workers(memory)) as pool:
        for path, ok, notes, output in pool.map(check, tests):
            if not ok:
                failed += 1
                print("FAIL", path.relative_to(ROOT), "-", "; ".join(notes))
                if args.verbose:
                    print(output)
    print(f"{'lint':24} {len(tests) - failed:4}/{len(tests)}")
    return 1 if failed and args.strict else 0


if __name__ == "__main__":
    sys.exit(main())
