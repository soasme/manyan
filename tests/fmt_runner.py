"""Run the formatter tests (tests/fmt) on Manyan, optionally validating with SANY.

usage: fmt_runner.py MANYAN [--oracle SANY] [--bless] [--only SUBSTRING] [--strict]

A test is NAME.tla, a module, with optional sibling NAME.files.
NAME.out is the expected formatted output (or `PARSE ERROR\\nexit 150\\n` for a
module with a syntax error). For each valid module, `-fmt` must:
  1. match NAME.out;
  2. be idempotent: formatting NAME.out produces NAME.out again;
  3. with --oracle, produce a module accepted by SANY.
"""
import argparse
import re
import shlex
import shutil
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from spec_runner import ROOT, guarded, workers

TESTS = ROOT / "tests/fmt"


def extract_comments(src):
    """Comments inside the outermost module, with trailing line spaces trimmed."""
    m = re.search(r"----+[ \t]*MODULE\b", src)
    if not m:
        return []
    i, n = m.start(), len(src)
    out, depth = [], 0
    while i < n:
        if src.startswith("----", i):
            j = i
            while j < n and src[j] == "-":
                j += 1
            k = j
            while k < n and src[k] in " \t":
                k += 1
            if src.startswith("MODULE", k) and (k + 6 == n or not (src[k + 6].isalnum() or src[k + 6] == "_")):
                depth += 1
            i = j
            continue
        if src.startswith("====", i):
            while i < n and src[i] == "=":
                i += 1
            depth -= 1
            if depth == 0:
                break
            continue
        if src[i] == '"':
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == "\\" else 1
            i += 1
            continue
        if src.startswith("\\*", i):
            s = i
            while i < n and src[i] != "\n":
                i += 1
            out.append(src[s:i].rstrip())
            continue
        if src.startswith("(*", i):
            s, cd = i, 0
            while i < n:
                if src.startswith("(*", i):
                    cd += 1
                    i += 2
                elif src.startswith("*)", i):
                    cd -= 1
                    i += 2
                    if cd == 0:
                        break
                else:
                    i += 1
            out.append("\n".join(line.rstrip() for line in src[s:i].splitlines()))
            continue
        i += 1
    return out


NOISE = re.compile(r"^(GuardMalloc\[|Sysctl \(debug\.toggle_address_reuse\))")


def strip_noise(text):
    return "".join(line for line in text.splitlines(True) if not NOISE.match(line))


def run_fmt(command, path, directory, memory):
    _, output, code, killed = guarded(command + ["-fmt", path.name], directory, 60, memory, b"")
    if killed:
        return None, f"{killed}\n"
    output = strip_noise(output)
    if code != 0:
        if code == 150 and "***Parse Error***" in output:
            return f"PARSE ERROR\nexit {code}\n", output
        return f"exit {code}\n{output}", output
    return output, output


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
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp).resolve()
            shutil.copy(path, directory / path.name)
            files = path.with_suffix(".files")
            if files.is_dir():
                shutil.copytree(files, directory, dirs_exist_ok=True)
            actual, output = run_fmt(engine, path, directory, memory)
            if args.bless and actual is not None:
                expected_path.write_text(actual)
            if not expected_path.exists():
                return path, False, ["no " + expected_path.name], output
            expected = expected_path.read_text()
            if actual != expected:
                notes.append("output differs")
            if actual is not None and not actual.startswith("PARSE ERROR\n"):
                if extract_comments(path.read_text()) != extract_comments(actual):
                    notes.append("comments changed")
                (directory / path.name).write_text(actual)
                again, _ = run_fmt(engine, path, directory, memory)
                if again != actual:
                    notes.append("not idempotent")
                if oracle:
                    _, sout, scode, skilled = guarded(oracle + ["-error-codes", path.name], directory, 60, memory)
                    if skilled or scode != 0:
                        notes.append(f"SANY failed ({skilled or scode})")
                        output += "\n--- SANY ---\n" + sout
        return path, not notes, notes, output

    failed = 0
    with ThreadPoolExecutor(max_workers=1 if args.oracle else workers(memory)) as pool:
        for path, ok, notes, output in pool.map(check, tests):
            if not ok:
                failed += 1
                print("FAIL", path.relative_to(ROOT), "-", "; ".join(notes))
                if args.verbose:
                    print(output)
    print(f"{'fmt':24} {len(tests) - failed:4}/{len(tests)}")
    return 1 if failed and args.strict else 0


if __name__ == "__main__":
    sys.exit(main())
