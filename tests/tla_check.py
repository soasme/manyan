"""Check manyan against the TLA+ models of its algorithms (tests/tla).

usage: tla_check.py ENGINE [--tlc "TLC CMD"] [--graphs N] [--seed S]

Each tests/tla/MCNAME.tla is a model, with its configuration after the
module as in tests/spec. The engine, and TLC when given, must check it
without error and print the same report.

Then the engine runs on N random state graphs, and the search it did must
be one the model BFS allows: the model (checked by TLC when given, else by
the engine) must reach the engine's result. A violation fixes the length
of its trace; a search without error fixes the counts and the depth.
The models, then the graphs, are checked as many at once as keep each
TLC's JVM, as 1000 MB, to half the machine's memory.
"""
import argparse
import random
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests"))
import spec_runner  # noqa: E402

TLA = ROOT / "tests/tla"


def check(command, name, directory):
    done = subprocess.run(command + ["-config", name + ".cfg", name], cwd=directory,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return spec_runner.normalize(done.stdout, directory) + f"exit {done.returncode}\n"


def tlc_command(tlc):
    return tlc.split() + ["-workers", "1", "-metadir", spec_runner.metadir()]


POOL = spec_runner.workers(1000)


def model(engine, tlc, path):
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        spec_runner.stage(path, directory)
        for other in TLA.glob("*.tla"):
            if other != path:
                (directory / other.name).write_text(other.read_text())
        mine = check(engine, path.stem, directory)
        ok = "No error has been found" in mine
        if tlc:
            ok = ok and check(tlc_command(tlc), path.stem, directory) == mine
        return ok, mine


def models(engine, tlc):
    failed = 0
    paths = sorted(TLA.glob("MC*.tla"))
    with ThreadPoolExecutor(POOL) as pool:
        for path, (ok, mine) in zip(paths, pool.map(lambda p: model(engine, tlc, p), paths)):
            failed += not ok
            print("ok  " if ok else "FAIL", path.relative_to(ROOT))
            if not ok:
                print(mine)
    return failed


def graph_spec(n, succ, init, bad):
    sets = lambda s: "{" + ", ".join(map(str, sorted(s))) + "}"
    return (f"---- MODULE G ----\nEXTENDS Naturals\nVARIABLE s\n"
            f"Succ == <<{', '.join(sets(x) for x in succ)}>>\n"
            f"Init == s \\in {sets(init)}\nNext == s' \\in Succ[s]\nInv == s \\notin {sets(bad)}\n====\n",
            "INIT Init\nNEXT Next\nINVARIANT Inv\n")


def run_graph(engine, n, succ, init, bad):
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        spec, cfg = graph_spec(n, succ, init, bad)
        (directory / "G.tla").write_text(spec)
        (directory / "G.cfg").write_text(cfg)
        out = check(engine, "G", directory)
    trace = len(re.findall(r"^State \d+:", out, flags=re.M))
    if "is violated" in out:
        return f'result = "invariant" /\\ trace = {trace or 1}'
    if "Deadlock reached" in out:
        return f'result = "deadlock" /\\ trace = {trace}'
    generated, distinct = map(int, re.search(r"(\d+) states generated, (\d+) distinct", out).groups())
    depth = int(re.search(r"depth of the complete state graph search is (\d+)", out).group(1))
    return (f'result = "ok" /\\ generated = {generated} /\\ Cardinality(DOMAIN seen) = {distinct}'
            f' /\\ level = {depth}')


def allowed(checker, n, succ, init, bad, outcome):
    """Whether the model BFS reaches the outcome on the graph."""
    sets = lambda s: "{" + ", ".join(map(str, sorted(s))) + "}"
    graph = (f"[succ |-> <<{', '.join(sets(x) for x in succ)}>>, init |-> {sets(init)}, "
             f"bad |-> {sets(bad)}]")
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        (directory / "BFS.tla").write_text((TLA / "BFS.tla").read_text())
        (directory / "R.tla").write_text(f"---- MODULE R ----\nEXTENDS BFS\nOne == {{{graph}}}\n"
                                         f"Other == ~({outcome})\n====\n")
        (directory / "R.cfg").write_text("CONSTANT Graphs <- One\nINIT Init\nNEXT Next\n"
                                         "INVARIANT Other\nCHECK_DEADLOCK FALSE\n")
        out = check(checker, "R", directory)
    return "Invariant Other is violated" in out


def graphs(engine, tlc, count, seed):
    rng = random.Random(seed)
    drawn = []
    for i in range(count):
        n = rng.randint(1, 6)
        succ = [{m for m in range(1, n + 1) if rng.random() < 0.35} for _ in range(n)]
        init = {m for m in range(1, n + 1) if rng.random() < 0.3} or {1}
        bad = {m for m in range(1, n + 1) if rng.random() < 0.15}
        drawn.append((n, succ, init, bad))

    def one(graph):
        checker = tlc_command(tlc) if tlc else engine   # TLC needs a fresh metadir for each run
        outcome = run_graph(engine, *graph)
        return outcome, allowed(checker, *graph, outcome)

    failed = 0
    with ThreadPoolExecutor(POOL) as pool:
        for (n, succ, init, bad), (outcome, ok) in zip(drawn, pool.map(one, drawn)):
            if not ok:
                failed += 1
                print("FAIL graph", succ, init, bad, "->", outcome)
    print(f"{count - failed}/{count} random graphs searched as the model allows")
    return failed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("engine")
    parser.add_argument("--tlc")
    parser.add_argument("--graphs", type=int, default=40)
    parser.add_argument("--seed", type=int, default=1)
    args = parser.parse_args()
    engine = [str(Path(args.engine).resolve())]
    failed = models(engine, args.tlc) + graphs(engine, args.tlc, args.graphs, args.seed)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
