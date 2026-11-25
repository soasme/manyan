"""Run the type checking tests (tests/typecheck) on Manyan, with Apalache as the oracle.

usage: typecheck_runner.py MANYAN [--oracle APALACHE] [--bless] [--only SUBSTRING] [--strict]

A test is NAME.tla, a module, with the modules it uses in NAME.files.
NAME.out is the outcome `apalache-mc typecheck` gives: Type checker [OK],
Type checker [FAILED] with the definitions whose types it could not
compute, or its typing input error; then the exit status. Manyan's
`-typecheck` prints the same lines; the messages that explain a type
error are not compared.

With --oracle, Apalache must give NAME.out too; --bless writes NAME.out
from it. Each run is killed past --memory MB resident (500, or 3000 with
Apalache's JVM), and only as many run at once as keep to half the
machine's memory.
"""
import argparse
import re
import shlex
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from spec_runner import ROOT, guarded, stage, workers

TESTS = ROOT / "tests/typecheck"


def outcome(output, code):
    output = re.sub(r"\s+[IEW]@[\d:.]+$", "", output, flags=re.M)
    error = re.search(r"^Typing input error: .*$", output, flags=re.M)
    if error:
        return f"{error.group(0)}\nexit {code}\n"
    if re.search(r"^Type checker \[OK\]$", output, flags=re.M):
        return f"Type checker [OK]\nexit {code}\n"
    failed = re.findall(r"Error when computing the type of (\S+)$", output, flags=re.M)
    if re.search(r"^Type checker \[FAILED\]$", output, flags=re.M):
        return f"Type checker [FAILED] {' '.join(failed)}\nexit {code}\n"
    return f"Failure {output.strip()[-200:]}\nexit {code}\n"


def run(command, path, oracle, memory):
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp).resolve()
        stage(path, directory)
        if oracle:
            args = command + ["typecheck", f"--out-dir={directory}/out", path.name]
        else:
            args = command + ["-typecheck", path.stem]
        _, output, code, killed = guarded(args, directory, 300, memory, b"")
        return (f"{killed}\n" if killed else outcome(output, code)), output


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
            reference, log = run(oracle, path, True, memory)
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
    with ThreadPoolExecutor(max_workers=workers(memory)) as pool:
        for path, ok, notes, output in pool.map(check, tests):
            if not ok:
                failed += 1
                print("FAIL", path.relative_to(ROOT), "-", "; ".join(notes))
                if args.verbose:
                    print(output)
    print(f"{'typecheck':24} {len(tests) - failed:4}/{len(tests)}")
    return 1 if failed and args.strict else 0


if __name__ == "__main__":
    sys.exit(main())
