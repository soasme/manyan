"""Check tlaplus/Examples' models with manyan and TLC; write docs/fullbench.md.

usage: examples.py ENGINE --tlc "TLC CMD" --examples DIR [--library DIR]...
                   [--only SUBSTRING] [--max-runtime HH:MM:SS] [--timeout S] [--memory MB]

Every exhaustive-search model whose recorded runtime is at most
--max-runtime (all of them, those with none recorded too, for `all`), and
every simulation and generation model, its behaviors
fixed by a seed and their number, runs once with each engine and one
worker, killed past --timeout seconds or --memory MB resident. manyan must
print what TLC prints.
Each library's modules are staged beside the spec unless the spec has one
of that name or manyan builds it in, as TLC finds them on its class path.
TLC's results are cached next to the Examples checkout: they change only
with the pins, and normalizing them again follows changes to normalize; a
run killed for time runs again under a longer --timeout. The diffs of the models that differ go to fullbench.diff.
"""
import argparse
import difflib
import hashlib
import json
import math
import platform
import re
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests"))
import spec_runner  # noqa: E402

BUILT_IN = {"Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "TLC", "Bags",
            "Randomization", "RealTime", "Toolbox", "TLCExt"}
COUNTS = re.compile(r"^(\d+) states generated, (\d+) distinct states found", re.M)


def run(command, directory, timeout, memory):
    """The seconds command takes and its output, or why it was killed."""
    seconds, output, code, killed = spec_runner.guarded(command, directory, timeout, memory)
    if killed:
        return seconds, None, killed
    return seconds, spec_runner.normalize(output, directory) + f"exit {code}\n", None


def stage(spec, libraries, directory):
    shutil.copytree(spec, directory)
    for library in libraries:
        for module in Path(library).glob("*.tla"):
            if module.stem not in BUILT_IN and not (directory / module.name).exists():
                shutil.copy(module, directory)


def options(model):
    """The engines' options for the model: a random one's behaviors fixed."""
    mode = model["mode"]
    if mode == "generate":
        return ["-generate", "num=100", "-seed", "1"]
    if isinstance(mode, dict) and "simulate" in mode:
        return ["-simulate", f"num={mode['simulate']['traceCount']}", "-seed", "1"]
    return []


def models(examples, only, max_runtime):
    for manifest in sorted(examples.glob("specifications/*/manifest.json")):
        for module in json.loads(manifest.read_text())["modules"]:
            for model in module["models"]:
                exhaustive = model["mode"] == "exhaustive search" and (
                    max_runtime == "all" or model["runtime"] != "unknown" and model["runtime"] <= max_runtime)
                if (exhaustive or options(model)) and only in model["path"]:
                    yield module, model


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("engine")
    parser.add_argument("--tlc", required=True)
    parser.add_argument("--examples", required=True, type=Path)
    parser.add_argument("--library", action="append", default=[])
    parser.add_argument("--only", default="")
    parser.add_argument("--max-runtime", default="00:10:00")
    parser.add_argument("--timeout", type=float, default=900)
    parser.add_argument("--memory", type=int, default=4000)
    args = parser.parse_args()
    engine = str(Path(args.engine).resolve())
    examples = args.examples.resolve()
    key = hashlib.sha1(f"{args.tlc} {examples} {args.library}".encode()).hexdigest()[:12]
    cache_path = examples.with_name(f"fullbench-tlc-{key}.json")
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    diffs = open(examples.with_name("fullbench.diff"), "w")
    rows, tallies, speedups = [], {}, []
    for module, model in models(examples, args.only, args.max_runtime):
        path = model["path"]
        name = path.removeprefix("specifications/").removesuffix(".cfg")
        command = options(model) + ["-config", Path(path).name, Path(module["path"]).stem]
        cached = " ".join([path] + options(model))
        java = ["-Dtlc2.tool.impl.Tool.cdot=true"] if "action composition" in module["features"] else []
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp).resolve() / "spec"
            stage(examples / Path(path).parent, args.library, directory)
            timed_out = cache.get(cached, {}).get("killed") or ""
            if cached not in cache or (timed_out.startswith("over") and timed_out.endswith(" s")
                                       and float(timed_out.split()[1]) < args.timeout):
                tlc = spec_runner.place(args.tlc.split(), java + ["-workers", "1", "-metadir", str(Path(tmp) / "meta")])
                seconds, output, killed = run(tlc + command, directory, args.timeout, args.memory)
                cache[cached] = {"seconds": seconds, "output": output, "killed": killed}
                cache_path.write_text(json.dumps(cache, indent=1))
            theirs = cache[cached]
            ours_seconds, ours, killed = run(spec_runner.place([engine], java) + command, directory, args.timeout, args.memory)
        if theirs["killed"]:
            verdict = f"TLC {theirs['killed']}"
        elif killed:
            verdict = f"manyan {killed}"
        elif ours != spec_runner.normalize(theirs["output"], directory):
            verdict = "differs"
            diffs.write(f"=== {name}\n" + "".join(difflib.unified_diff(
                theirs["output"].splitlines(True), ours.splitlines(True), "TLC", "manyan", n=2)))
            diffs.flush()
        else:
            verdict = "same"
            speedups.append(theirs["seconds"] / ours_seconds)
        tallies[verdict.split(" over")[0]] = tallies.get(verdict.split(" over")[0], 0) + 1
        counts = COUNTS.search(theirs["output"] or "")
        distinct = counts.group(2) if counts else ""
        manyan_time = "" if killed else f"{ours_seconds:.2f}"
        speedup = f"{theirs['seconds'] / ours_seconds:.1f}x" if verdict == "same" else ""
        rows.append(f"| {name} | {distinct} | {theirs['seconds']:.2f} | {manyan_time} | {speedup} | {verdict} |")
        print(rows[-1], flush=True)
    mean = math.exp(sum(map(math.log, speedups)) / len(speedups)) if speedups else 0
    summary = ", ".join(f"{n} {verdict}" for verdict, n in sorted(tallies.items(), key=lambda t: -t[1]))
    report = ROOT / "docs/fullbench.md"
    head = report.read_text().split("<!-- results -->")[0] if report.exists() else "# Full benchmark\n\n"
    report.write_text(head + "<!-- results -->\n\n"
                      f"tlaplus/Examples at {examples.name.removeprefix('Examples-')[:12]}, "
                      + ("every exhaustive-search model" if args.max_runtime == "all" else
                         f"the exhaustive-search models recorded to run in at most {args.max_runtime}")
                      + f" (each run killed past {args.timeout:.0f} s), and the simulation and generation "
                      f"models with `-seed 1` and `num=` their traceCount, or 100. Measured on {platform.machine()} "
                      f"{platform.system()} {platform.release()}, one run, wall-clock seconds, one worker.\n\n"
                      f"{len(rows)} models: {summary}. Where manyan prints what TLC prints, "
                      f"it is {mean:.1f}x as fast (geometric mean).\n\n"
                      "| model | distinct states | TLC | Manyan | speedup | result |\n"
                      "|---|---:|---:|---:|---:|---|\n" + "\n".join(rows) + "\n")
    return 0 if tallies.get("same", 0) + tallies.get("TLC", 0) == len(rows) else 1


if __name__ == "__main__":
    sys.exit(main())
