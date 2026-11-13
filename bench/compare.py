"""Time manyan against TLC on the specs in bench/ and write docs/benchmark.md.

usage: compare.py ENGINE --tlc "TLC CMD" [--runs N] [--only SUBSTRING]

Each bench/NAME.tla holds a module and, after it, its configuration, as in
tests/spec. Each engine runs with one worker and with one per core; each
manyan run must print what TLC prints with one worker (TLC's own parallel
runs may not: their search order, so their depth, varies). The time is
the best wall-clock time of N runs.
"""
import argparse
import os
import platform
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests"))
import spec_runner  # noqa: E402

COUNTS = re.compile(r"^(\d+) states generated, (\d+) distinct states found", re.M)


def measure(command, path, runs):
    best, output = None, ""
    for _ in range(runs):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp).resolve()
            spec_runner.stage(path, directory)
            start = time.perf_counter()
            done = subprocess.run(command + ["-config", path.stem + ".cfg", path.stem], cwd=directory,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            elapsed = time.perf_counter() - start
            output = spec_runner.normalize(done.stdout, directory) + f"exit {done.returncode}\n"
        best = elapsed if best is None else min(best, elapsed)
    return best, output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("engine")
    parser.add_argument("--tlc", required=True)
    parser.add_argument("--runs", type=int, default=10)
    parser.add_argument("--only", default="")
    args = parser.parse_args()
    engine = str(Path(args.engine).resolve())
    cores = os.cpu_count()
    rows, failed = [], False
    for path in sorted((ROOT / "bench").glob("*.tla")):
        if args.only not in path.stem:
            continue
        tlc = args.tlc.split() + ["-metadir", spec_runner.metadir(), "-workers"]
        tlc1, reference = measure(tlc + ["1"], path, args.runs)
        tlcn, _ = measure(tlc + [str(cores)], path, args.runs)
        ours1, ours1_out = measure([engine], path, args.runs)
        oursn, oursn_out = measure([engine, "-workers", str(cores)], path, args.runs)
        counts = COUNTS.search(reference)
        same = ours1_out == oursn_out == reference
        failed |= not same
        distinct = counts.group(2) if counts else "?"
        rows.append(f"| {path.stem} | {distinct} | {tlc1:.2f} | {ours1:.2f} | {tlc1 / ours1:.1f}x "
                    f"| {tlcn:.2f} | {oursn:.2f} | {tlcn / oursn:.1f}x |" + ("" if same else " output differs |"))
        print(rows[-1], flush=True)
    report = ROOT / "docs/benchmark.md"
    head = report.read_text().split("<!-- results -->")[0] if report.exists() else "# Benchmark\n\n"
    report.write_text(head + "<!-- results -->\n\n"
                      f"Measured on {platform.machine()} {platform.system()} {platform.release()}, "
                      f"best of {args.runs} runs, wall-clock seconds, with 1 worker and with {cores}.\n\n"
                      f"| spec | distinct states | TLC | Manyan | speedup | TLC ({cores}) | Manyan ({cores}) | speedup |\n"
                      "|---|---:|---:|---:|---:|---:|---:|---:|\n"
                      + "\n".join(rows) + "\n")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
