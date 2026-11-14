"""Run the specification tests (tests/spec) on a model checker.

usage: spec_runner.py "ENGINE [ARGS]" [--oracle TLC] [--bless] [--only SUBSTRING] [--strict]

A test is NAME.tla: a module, then, after the line that ends it, the model
configuration (SANY ignores text after a module). NAME.out is the
normalized output (docs/standards/tla2.md, 11.1) and exit status TLC gives.
Modules a test uses go in a sibling NAME.files directory. Each test is
staged in a temporary directory and run as `ENGINE OPTIONS -config
NAME.cfg NAME`, OPTIONS being those of a line `\\* options: ...` in it (which may give
its own -config; the configuration is also the engine's standard input, or
NAME.in where a test has one). The
oracle does not run a test with an option in ORACLE_SKIPS.
A state graph it dumps (`-dump dot FILE`) follows its output, its states
numbered in order of appearance, as fingerprints differ; then the
behaviors it writes (`-simulate file=FILE`) and the counterexample
(`-dumpTrace json FILE`). The time naming an `-inv` expression is N.

With --oracle, the oracle (a command running TLC) must produce NAME.out
too, which validates the test; --bless writes NAME.out from the oracle.
With --strict the exit status is nonzero when the engine fails any test.
Each run is killed past --memory MB resident (1000, or 3000 with an
oracle), and only as many run at once as keep to half the machine's memory.
"""
import argparse
import atexit
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC = ROOT / "tests/spec"

NOISE = re.compile(
    r"^(TLC2 Version|manyan version|Running |Parsing file|Semantic processing|Starting\.\.\.|"
    r"Computing initial states\.\.\.|Computed \d+ initial states|Progress\(|Checking temporal properties for|"
    r"Finished checking temporal properties|Implied-temporal checking|Finished in|"
    r"The average outdegree|  Estimates of the probability|  because two distinct states|"
    r"  calculated \(optimistic\)|  based on the actual fingerprints|Checking \d+ branches of temporal properties|"
    r"Warning: Please run the Java VM|GuardMalloc\[|"
    r"Progress: \d+ states checked|The number of states generated: |Simulation using seed |"
    r"Linting of module|Trace exploration spec path: )")
# TLC's warning that its heap is small depends on the machine.
LOW_MEMORY = re.compile(
    r"^Warning: Liveness checking will be extremely slow because TLC is running low on memory\.\n"
    r"Try allocating more memory to the Java pool \(heap\) in future TLC runs\.\n"
    r"(\(Use the -nowarning option to disable this warning\.\)\n)?", re.M)


OUTPUT_LIMIT = 64 << 20

# Options a test may give that the oracle cannot run: TLC reads a
# configuration only from a file whose name ends in .cfg, and has no -stack.
ORACLE_SKIPS = {"-config", "-stack"}


def guarded(command, directory, timeout, memory, input=None):
    """The seconds command takes, its output and exit status, or why it was
    killed: past timeout seconds, memory MB resident (with what it starts),
    or OUTPUT_LIMIT bytes of output. input, if given, is its standard input."""
    start = time.perf_counter()
    try:
        process = subprocess.Popen(command, cwd=directory, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   stdin=None if input is None else subprocess.PIPE, start_new_session=True)
    except OSError as error:
        return 0, f"{error}\n", "error", None
    chunks, size = [], [0]

    def pump():
        for chunk in iter(lambda: process.stdout.read(1 << 16), b""):
            size[0] += len(chunk)
            if size[0] <= OUTPUT_LIMIT:
                chunks.append(chunk)
    reader = threading.Thread(target=pump)
    reader.start()
    if input is not None:
        try:
            process.stdin.write(input)
            process.stdin.close()
        except BrokenPipeError:   # it ended without reading
            pass
    killed, wait = None, 0.01
    while not finished(process, wait):
        wait = min(2 * wait, 0.25)
        if resident(process.pid) > memory * 1024:
            killed = f"over {memory} MB"
        elif time.perf_counter() - start > timeout:
            killed = f"over {timeout} s"
        elif size[0] > OUTPUT_LIMIT:
            killed = f"over {OUTPUT_LIMIT >> 20} MB of output"
        if killed:
            os.killpg(process.pid, signal.SIGKILL)
            break
    process.wait()
    reader.join()
    return time.perf_counter() - start, b"".join(chunks).decode(errors="replace"), process.returncode, killed


def resident(group):
    """The KB a process group holds resident; 0 where ps cannot say (Cygwin)."""
    try:
        rss = subprocess.run(["ps", "-o", "rss=", "-g", str(group)], capture_output=True, text=True).stdout
    except OSError:
        return 0
    return sum(int(w) for w in rss.split() if w.isdigit())


def finished(process, seconds):
    try:
        process.wait(seconds)
        return True
    except subprocess.TimeoutExpired:
        return False


def workers(memory, most=8):
    """At most most runs at once, of memory MB each, within half the machine's memory."""
    try:
        total = os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") >> 20
    except (AttributeError, ValueError, OSError):
        return most
    return max(1, min(most, total // 2 // memory))


def normalize(output, directory):
    if "Error: Parsing or semantic analysis failed." in output:
        return "Error: Parsing or semantic analysis failed.\n"
    output = LOW_MEMORY.sub("", output)
    lines = []
    nested = False
    for line in output.replace(str(directory) + "/", "").splitlines():
        if line.startswith("Error: The error occurred when TLC was evaluating the nested"):
            nested = True
        if nested:
            nested = line.strip() != ""
            continue
        if NOISE.match(line):
            continue
        line = re.sub(r" at \d{4}-\d\d-\d\d \d\d:\d\d:\d\d\.$", ".", line)
        line = re.sub(r"(__Debugger(Module|Expr)__)\d+", r"\1N", line)
        if line.strip() == "" and (not lines or lines[-1] == ""):
            continue
        lines.append(line.rstrip())
    while lines and lines[-1] == "":
        lines.pop()
    return "\n".join(lines) + "\n"


def dumped(directory, options):
    """The files a run wrote in directory: dot files, each state's fingerprint
    replaced by its number, behaviors, user output and the counterexample."""
    text = ""
    for dot in sorted(directory.glob("*.dot")):
        ids = {}
        number = lambda m: m.group(1) + "s%d" % ids.setdefault(m.group(2), len(ids))
        text += f"--- {dot.name}\n"
        for line in dot.read_text().splitlines():
            pattern = r"([ ;]|^)(-?\d+)(?=;)" if line.startswith("{rank") else r"(^|-> )(-?\d+)(?= )"
            text += re.sub(pattern, number, line) + "\n"
    for written in sorted(directory.glob("*_0_*")) + sorted(directory.glob("*.txt")):   # -simulate file=, -userFile
        text += f"--- {written.name}\n" + written.read_text()
    for i, option in enumerate(options[:-2]):
        if option == "-dumpTrace" and (directory / options[i + 2]).exists():
            text += f"--- {options[i + 2]}\n" + (directory / options[i + 2]).read_text() + "\n"
    return text


def stage(path, directory):
    text = path.read_text()
    ends = list(re.finditer(r"^====+[ \t]*$", text, flags=re.M))
    config = text[ends[-1].end():].lstrip("\n") if ends else ""
    shutil.copy(path, directory / path.name)
    (directory / (path.stem + ".cfg")).write_text(config)
    files = path.with_suffix(".files")
    if files.is_dir():
        shutil.copytree(files, directory, dirs_exist_ok=True)


def options(path):
    """The engine options a test names on a line `\\* options: -simulate ...`."""
    found = re.search(r"^\\\* options: (.*)$", path.read_text(), flags=re.M)
    return shlex.split(found.group(1)) if found else []


def place(command, options):
    """command with options: TLC takes Java's -Dk=v before its class."""
    if "tlc2.TLC" not in command:
        return command + options
    at = command.index("tlc2.TLC")
    java = [o for o in options if o.startswith("-D")]
    return command[:at] + java + command[at:] + [o for o in options if o not in java]


def run(command, path, memory):
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp).resolve()
        stage(path, directory)
        named = options(path)
        config = [] if "-config" in named else ["-config", path.stem + ".cfg"]
        # The configuration is also the engine's standard input, a pipe for
        # `-config /dev/stdin`, but for a test that gives its own.
        given = path.with_suffix(".in")
        _, output, code, killed = guarded(place(command, named) + config + [path.stem], directory, 300, memory,
                                          (given if given.exists() else directory / (path.stem + ".cfg")).read_bytes())
        if killed:
            output, code = f"{killed}\n", "killed"
        return normalize(output, directory) + f"exit {code}\n" + dumped(directory, named)


def metadir():
    """A fresh directory for TLC's -metadir, removed at exit."""
    meta = tempfile.mkdtemp(prefix="manyan-meta-")
    atexit.register(shutil.rmtree, meta, True)
    return meta


def oracle_command(tlc):
    return tlc.split() + ["-workers", "1", "-metadir", metadir()]


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
    tests = sorted(p for p in SPEC.rglob("*.tla") if ".files" not in str(p) and args.only in str(p))

    def check(path):
        expected_path = path.with_suffix(".out")
        notes = []
        if args.oracle and not ORACLE_SKIPS & set(options(path)):
            reference = run(oracle_command(args.oracle), path, memory)
            if args.bless:
                expected_path.write_text(reference)
            elif not expected_path.exists() or reference != expected_path.read_text():
                notes.append("oracle disagrees with " + expected_path.name)
        expected = expected_path.read_text() if expected_path.exists() else None
        if expected is None:
            return path, False, ["no " + expected_path.name], ""
        actual = run(engine, path, memory)
        if actual != expected:
            notes.append("output differs")
        return path, not notes, notes, actual if actual != expected else ""

    failed = 0
    chapters = {}
    # TLC unpacks its standard modules into one shared directory, so it runs alone.
    with ThreadPoolExecutor(max_workers=1 if args.oracle else workers(memory)) as pool:
        for path, ok, notes, actual in pool.map(check, tests):
            chapter = path.parent.relative_to(SPEC).as_posix()
            passed, total = chapters.get(chapter, (0, 0))
            chapters[chapter] = (passed + ok, total + 1)
            if not ok:
                failed += 1
                print("FAIL", path.relative_to(ROOT), "-", "; ".join(notes))
                if args.verbose and actual:
                    print(actual)
    for chapter, (passed, total) in sorted(chapters.items()):
        print(f"{chapter:24} {passed:4}/{total}")
    print(f"{'total':24} {len(tests) - failed:4}/{len(tests)}")
    return 1 if failed and args.strict else 0


if __name__ == "__main__":
    sys.exit(main())
