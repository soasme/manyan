"""A check killed after a checkpoint goes on from it to what a check not
stopped prints, but the initial states, which it does not compute again.

usage: recover_runner.py MANYAN

Each case checks MODEL with checkpoints (-checkpoint), is killed after
one, and goes on from it (-recover), with the options of each
side: other workers, a compressed checkpoint (-gzip), the states in files
(-metadir), temporal properties that hold and fail. The model's strings are made as it is checked, so the
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
vars == <<x, y, w, z>>
Spec == Init /\\ [][Next]_vars
Holds == <>[](x + y + w >= 0)
Fails == <>(x + y + w = 1000)
====
"""
CONFIGS = {"invariant": "INIT Init\nNEXT Next\nINVARIANT Inv\n", "deadlock": "INIT Init\nNEXT Next\n",
           "holds": "SPECIFICATION Spec\nPROPERTY Holds\n", "fails": "SPECIFICATION Spec\nPROPERTY Fails\n"}
EVERY = ["-checkpoint", "0.000001"]   # each 256 states and level
CASES = [  # the config, the options checkpointing, the checkpoint killed after, the options recovering
    ("invariant", EVERY, 40, []),
    ("invariant", EVERY + ["-workers", "4"], 40, ["-workers", "3"]),
    ("invariant", EVERY, 40, ["-workers", "2"]),
    ("invariant", EVERY + ["-gzip"], 40, []),
    ("deadlock", EVERY + ["-metadir", "meta"], 40, ["-metadir", "meta", "-workers", "4"]),
    ("holds", ["-checkpoint", "0.002"], 3, []),   # past the checks of liveness at 2^16 states and 2^17
    ("fails", ["-checkpoint", "0.002", "-workers", "4"], 3, []),
]


def killed(command, directory, last):
    """The run directory of its checkpoint `last`, after which it was killed."""
    run, n = None, 0
    with subprocess.Popen(command, cwd=directory, stdout=subprocess.PIPE, text=True) as p:
        for line in p.stdout:
            if line.startswith("Checkpointing of run "):
                run = line.removeprefix("Checkpointing of run ").strip()
            n += line.startswith("Checkpointing completed")
            if n == last:
                p.send_signal(signal.SIGKILL)
                break
    return run if n == last else None


def main():
    engine = shlex.split(sys.argv[1])
    engine[0] = str(Path(engine[0]).resolve())
    passed = 0
    for config, checkpointing, last, recovering in CASES:
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "R.tla").write_text(MODEL)
            (Path(tmp) / "R.cfg").write_text(CONFIGS[config])
            check = lambda options: subprocess.run(engine + options + ["R"], cwd=tmp, capture_output=True, text=True).stdout
            extra = [] if config == "invariant" else ["-deadlock"]
            want = [l for l in check(extra + recovering).splitlines() if not l.startswith("Finished computing initial")]
            run = killed(engine + extra + checkpointing + ["R"], tmp, last)
            got = check(extra + recovering + ["-recover", run]).splitlines() if run else []
            same = got[1:3] and got[1].startswith("Starting recovery") and got[2].startswith("Recovery completed") and got[:1] + got[3:] == want
            passed += bool(same)
            if not same:
                print(f"FAIL {config} {' '.join(checkpointing)} / {' '.join(recovering)}: " + (f"{got[:3]}" if run else f"no checkpoint {last}"))
    print(f"recover {passed:>21}/{len(CASES)}")
    sys.exit(passed != len(CASES))


main()
