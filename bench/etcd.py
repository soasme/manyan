"""Validate etcd's raft traces with manyan and TLC; write docs/etcd.md.

usage: etcd.py ENGINE --tlc "TLC CMD" --raft DIR [--library DIR]...
               [--only SUBSTRING] [--timeout S] [--memory MB]

etcd checks its raft library's traces against its spec with TLC
(tla/validate.sh). This logs a trace from each of the library's
interaction tests, in a copy of the checkout given a TraceLogger, which
needs Go; with tla/example.ndjson, each is validated once by each engine
as validate.sh runs TLC, killed past --timeout seconds or --memory MB
resident. manyan must print what TLC prints. TLC's results are cached
next to the checkout.
"""
import argparse
import difflib
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "bench"))
sys.path.insert(0, str(ROOT / "tests"))
import examples  # noqa: E402
import spec_runner  # noqa: E402

OPTIONS = ["-config", "Traceetcdraft.cfg", "Traceetcdraft.tla", "-lncheck", "final", "-fpmem", "0.9"]

# What the interaction tests are given to log each event as an NDJSON line.
LOGGER = '''
type traceLogger struct{ enc *json.Encoder }

func (l *traceLogger) TraceEvent(ev *raft.TracingEvent) {
	l.enc.Encode(map[string]any{"tag": "trace", "event": ev})
}
'''


def log_traces(raft, out):
    """Runs the interaction tests of a copy of raft, each writing its trace to out."""
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "raft"
        shutil.copytree(raft, copy, ignore=shutil.ignore_patterns(".git"))
        test = copy / "interaction_test.go"
        source = test.read_text().replace('import (\n', 'import (\n\t"encoding/json"\n\t"os"\n\t"path/filepath"\n\t"strings"\n', 1)
        source = source.replace(
            "\t\tenv := rafttest.NewInteractionEnv(&rafttest.InteractionOpts{\n",
            '\t\tf, err := os.Create(filepath.Join(os.Getenv("TRACE_DIR"), '
            'strings.TrimSuffix(filepath.Base(path), ".txt")+".ndjson"))\n'
            "\t\tif err != nil {\n\t\t\tt.Fatal(err)\n\t\t}\n\t\tdefer f.Close()\n"
            "\t\tlg := &traceLogger{json.NewEncoder(f)}\n"
            "\t\tenv := rafttest.NewInteractionEnv(&rafttest.InteractionOpts{\n"
            "\t\t\tOnConfig: func(c *raft.Config) { c.TraceLogger = lg },\n", 1)
        test.write_text(source + LOGGER)
        subprocess.run(["go", "test", "-tags", "with_tla", "-run", "TestInteraction", "-count=1", "."],
                       cwd=copy, env=dict(os.environ, TRACE_DIR=str(out)), check=True, stdout=subprocess.DEVNULL)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("engine")
    parser.add_argument("--tlc", required=True)
    parser.add_argument("--raft", required=True, type=Path)
    parser.add_argument("--library", action="append", default=[])
    parser.add_argument("--only", default="")
    parser.add_argument("--timeout", type=float, default=3600)
    parser.add_argument("--memory", type=int, default=4000)
    args = parser.parse_args()
    engine = str(Path(args.engine).resolve())
    raft = args.raft.resolve()
    key = hashlib.sha1(f"{args.tlc} {raft} {args.library}".encode()).hexdigest()[:12]
    cache_path = raft.with_name(f"etcd-tlc-{key}.json")
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    diffs = open(raft.with_name("etcd.diff"), "w")
    rows, same = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp).resolve()
        traces = tmp / "traces"
        traces.mkdir()
        log_traces(raft, traces)
        shutil.copy(raft / "tla/example.ndjson", traces)
        directory = tmp / "spec"
        examples.stage(raft / "tla", args.library, directory)
        for trace in sorted(traces.glob("*.ndjson"), key=lambda t: t.stat().st_size):
            name = trace.stem
            if args.only not in name:
                continue
            os.environ["JSON"] = str(trace)
            meta = ["-metadir", str(tmp / "meta")]
            if name not in cache:
                seconds, output, killed = examples.run(args.tlc.split() + OPTIONS + meta, directory,
                                                       args.timeout, args.memory)
                cache[name] = {"seconds": seconds, "output": output, "killed": killed}
                cache_path.write_text(json.dumps(cache, indent=1))
            theirs = cache[name]
            ours_seconds, ours, killed = examples.run([engine] + OPTIONS + meta, directory, args.timeout, args.memory)
            if theirs["killed"]:
                verdict = f"TLC {theirs['killed']}"
            elif killed:
                verdict = f"manyan {killed}"
            elif ours != theirs["output"]:
                verdict = "differs"
                diffs.write(f"=== {name}\n" + "".join(difflib.unified_diff(
                    theirs["output"].splitlines(True), ours.splitlines(True), "TLC", "manyan", n=2)))
                diffs.flush()
            else:
                verdict = "same"
                same += 1
            events = sum(1 for _ in open(trace))
            status = (theirs["output"] or "").strip().splitlines()[-1:] or [""]
            manyan_time = "" if killed else f"{ours_seconds:.2f}"
            rows.append(f"| {name} | {events} | {status[0]} | {theirs['seconds']:.2f} | {manyan_time} | {verdict} |")
            print(rows[-1], flush=True)
    rev = subprocess.run(["git", "-C", str(raft), "rev-parse", "HEAD"], capture_output=True, text=True).stdout[:12]
    report = ROOT / "docs/etcd.md"
    head = report.read_text().split("<!-- results -->")[0] if report.exists() else "# etcd's trace validation\n\n"
    report.write_text(head + "<!-- results -->\n\n"
                      f"etcd-io/raft at {rev or raft.name}: the traces its interaction tests log, and "
                      f"`tla/example.ndjson`. Measured on {platform.machine()} {platform.system()} "
                      f"{platform.release()}, one run, wall-clock seconds, one worker.\n\n"
                      f"{len(rows)} traces: manyan prints what TLC prints for {same}.\n\n"
                      "| trace | events | TLC's exit | TLC | Manyan | result |\n"
                      "|---|---:|---|---:|---:|---|\n" + "\n".join(rows) + "\n")
    return 0 if same == len(rows) else 1


if __name__ == "__main__":
    sys.exit(main())
