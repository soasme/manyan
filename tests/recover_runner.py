"""A check killed after a checkpoint goes on from it to what a check not
stopped prints, but the initial states, which it does not compute again.

usage: recover_runner.py MANYAN

Each case checks MODEL with checkpoints (-checkpoint), is killed after
the 40th, and goes on from the last (-recover), with the options of each
side: other workers, a compressed checkpoint (-gzip), the states in files
(-metadir). The model's strings are made as it is checked, so the
checkpoint keeps their order; its levels are wide enough for workers.
"""
import shlex
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

MODEL = """---- MODULE R ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x, y, w, z
Init == x = 0 /\\ y = 0 /\\ w = 0 /\\ z = {}
Next == /\\ x < 60 /\\ y < 60 /\\ w < 60
        /\\ \\/ x' = x + 1 /\\ UNCHANGED <<y, w>>
           \\/ y' = y + 1 /\\ UNCHANGED <<x, w>>
           \\/ w' = w + 1 /\\ UNCHANGED <<x, y>>
        /\\ z' = IF (x + w) % 40 = 0 THEN z \\cup {ToString(y % 5) \\o "s"} ELSE z
Inv == x + y + w < 150
====
"""
CONFIGS = {"invariant": "INIT Init\nNEXT Next\nINVARIANT Inv\n", "deadlock": "INIT Init\nNEXT Next\n"}
CASES = [  # the config, the options checkpointing, the options recovering
    ("invariant", [], []),
    ("invariant", ["-workers", "4"], ["-workers", "3"]),
    ("invariant", [], ["-workers", "2"]),
    ("invariant", ["-gzip"], []),
    ("deadlock", ["-metadir", "meta"], ["-metadir", "meta", "-workers", "4"]),
]


def killed(command, directory):
    """The run directory of the last checkpoint before it was killed."""
    run, n = None, 0
    with subprocess.Popen(command, cwd=directory, stdout=subprocess.PIPE, text=True) as p:
        for line in p.stdout:
            if line.startswith("Checkpointing of run "):
                run = line.removeprefix("Checkpointing of run ").strip()
            n += line.startswith("Checkpointing completed")
            if n == 40:
                p.send_signal(signal.SIGKILL)
                break
    return run if n == 40 else None


def main():
    engine = shlex.split(sys.argv[1])
    engine[0] = str(Path(engine[0]).resolve())
    passed = 0
    for config, checkpointing, recovering in CASES:
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "R.tla").write_text(MODEL)
            (Path(tmp) / "R.cfg").write_text(CONFIGS[config])
            check = lambda options: subprocess.run(engine + options + ["R"], cwd=tmp, capture_output=True, text=True).stdout
            extra = ["-deadlock"] if config == "deadlock" else []
            want = [l for l in check(extra + recovering).splitlines() if not l.startswith("Finished computing initial")]
            run = killed(engine + extra + checkpointing + ["-checkpoint", "0.000001", "R"], tmp)
            got = check(extra + recovering + ["-recover", run]).splitlines() if run else []
            same = got[1:3] and got[1].startswith("Starting recovery") and got[2].startswith("Recovery completed") and got[:1] + got[3:] == want
            passed += bool(same)
            if not same:
                print(f"FAIL {config} {' '.join(checkpointing)} / {' '.join(recovering)}: " + (f"{got[:3]}" if run else "no 40th checkpoint"))
    print(f"recover {passed:>21}/{len(CASES)}")
    sys.exit(passed != len(CASES))


main()
