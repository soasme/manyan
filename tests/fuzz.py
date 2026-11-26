"""Fuzz manyan.

usage: fuzz.py crash ENGINE [--runs N] [--seed S]
       fuzz.py fmt ENGINE [--sany "SANY CMD"] [--runs N] [--seed S]
       fuzz.py lint ENGINE [--sany "SANY CMD"] [--runs N] [--seed S]
       fuzz.py typecheck ENGINE [--runs N] [--seed S]
       fuzz.py sym ENGINE [--runs N] [--seed S]
       fuzz.py diff ENGINE --tlc "TLC CMD" [--runs N] [--seed S]
       fuzz.py sim ENGINE --tlc "TLC CMD" [--runs N] [--seed S]
       fuzz.py check ENGINE --tlc "TLC CMD" [--runs N] [--seed S]
       fuzz.py live ENGINE --tlc "TLC CMD" [--runs N] [--seed S]
       fuzz.py prove ENGINE --tlapm TLAPM [--runs N] [--seed S]
       fuzz.py ref ENGINE --ref REF [--runs N] [--seed S]

crash: mutates the models of tests/spec and runs the engine (a sanitizer
build) on each, half of them as random simulations (-simulate or
-generate); it must exit with one of its statuses, without a signal or a
sanitizer report.

fmt: mutates modules from tests/fmt, tests/lint and tests/spec and runs
`ENGINE -fmt` (a sanitizer build) on each; it must exit 0 or 150 without
a signal, timeout or sanitizer report, and every module that formats must
be idempotent and preserve all comments. With --sany, every SANY-valid
input must also format to a SANY-valid module.

lint: mutates modules from tests/lint and tests/spec and runs
`ENGINE -lint` (a sanitizer build) on each; it must exit 0 or 150 without
a signal, timeout or sanitizer report. With --sany, also generates tricky
grammar and level cases and compares `-lint` outcomes against SANY.

typecheck: mutates modules from tests/typecheck and tests/symbolic and
runs `ENGINE -typecheck` (a sanitizer build) on each; it must exit in
{0, 120, 150, 255} without a signal, timeout or sanitizer report.

sym: generates small typed finite-state specs and compares
`ENGINE -symbolic -length K` against explicit `ENGINE` (safety, deadlock,
and temporal properties).

sim: runs models of tests/spec as random simulations (-simulate or
-generate, sometimes with -continue), with random seeds and depths, with
the engine and with TLC; they must print the same.

check: checks models of tests/spec with random options (-deadlock,
-continue, -difftrace, -nowarning, -view), the engine with one or four
workers, and with TLC; they must print the same.

live: checks a random temporal property (including constants, ~, LET,
nested WF/SF, keyword subscripts, level-0 overrides, higher-order
actions, INSTANCE, and nested ~>) of a random state graph under random
fairness with the engine and with TLC, both with the same random
fingerprint polynomial (-fp); they must print the same.

prove: makes random constant expressions, evaluates each with the engine,
and asks TLAPS (--tlapm) to prove that the expression equals the value
printed, or else that it does not. A proof of the negation is a finding:
the engine's value contradicts TLA+'s semantics, whatever TLC prints.
What TLAPS proves neither way is inconclusive and left out.

ref: makes the expressions of prove and asks REF, the reference semantics
of lean/, whether each equals the value the engine prints. Another value
is a finding; an expression whose value TLA+ leaves unspecified, or the
reference cannot compute, is left out.

diff: makes random constant expressions (including lazy functions in
sets, out-of-domain EXCEPT, nested @, empty lazy sets, and AssertError
recovery) and small CONSTANT/Init/Next/SYMMETRY models, checking them
with the engine and with TLC; they must print the same.
"""
import argparse
import random
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests"))
import spec_runner  # noqa: E402

MEMORY = 3000   # MB, for TLC too
STATUSES = {0, 10, 11, 12, 13, 14, 75, 76, 77, 150, 151, 255}
TC_STATUSES = {0, 120, 150, 255}
STRINGS = ['"a"', '"b"', '"ab"', '""']
TOKEN = re.compile(r"\\[A-Za-z]+|[A-Za-z_][A-Za-z0-9_]*|\d+|\"[^\"\n]*\"|<<|>>|\|->|==|/\\|\\/|~>|\[\]|<>|::|:>|@@|[^\s\w]|\s+")
VOCAB = {
    "word": [
        "TRUE", "FALSE", "BOOLEAN", "STRING", "Nat", "Int", "SUBSET", "UNION",
        "DOMAIN", "EXCEPT", "LET", "IN", "CASE", "OTHER", "CHOOSE", "ENABLED",
        "UNCHANGED", "LAMBDA", "RECURSIVE", "INSTANCE", "WITH", "IF", "THEN",
        "ELSE", "IsFiniteSet", "PrintT",
    ],
    "symbol": [
        "~>", "[]", "<>", "::", "@", "|->", ":>", "@@", "/\\", "\\/", "\\in",
        "\\notin", "\\cup", "\\cap", "\\", "\\X", "->", "'", "<<", ">>",
    ],
    "number": ["0", "1", "-1", "2147483648"],
    "string": ['""', '"a"', '"\\""', '"a\\nb"'],
}


def kind(token):
    if token[0].isdigit():
        return "number"
    if token[0].isalpha() or token[0] == "_":
        return "word"
    if token[0] == '"':
        return "string"
    return "symbol"


def mutate(text, rng):
    """Mostly swaps a token for another of its kind (or from VOCAB), so most mutants parse."""
    tokens = TOKEN.findall(text)
    spots = [i for i, t in enumerate(tokens) if not t.isspace()]
    if not spots:
        return text
    by_kind = {}
    for i in spots:
        by_kind.setdefault(kind(tokens[i]), []).append(tokens[i])
    for _ in range(rng.randint(1, 3)):
        i = rng.choice(spots)
        if not tokens[i]:
            continue
        choice = rng.random()
        if choice < 0.55:
            k = kind(tokens[i])
            tokens[i] = str(rng.randint(0, 12)) if k == "number" else rng.choice(by_kind[k])
        elif choice < 0.75:
            k = kind(tokens[i])
            tokens[i] = rng.choice(VOCAB[k])
        elif choice < 0.88:
            tokens[i] = ""
        else:
            tokens[i] = tokens[i] + " " + rng.choice([tokens[rng.choice(spots)], rng.choice(VOCAB["word"]), rng.choice(VOCAB["symbol"])])
    return "".join(tokens)


def run(engine, name, directory, timeout, options=()):
    try:
        done = subprocess.run(engine + list(options) + ["-config", name + ".cfg", name], cwd=directory, timeout=timeout,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace")
    except subprocess.TimeoutExpired:
        return None, ""
    return done.returncode, done.stdout


def crash(engine, runs, seed):
    rng = random.Random(seed)
    seeds = sorted((ROOT / "tests/spec").rglob("*.tla"))
    seeds = [p for p in seeds if p.suffixes == [".tla"] and ".files" not in str(p)]
    failed = timeouts = 0
    for i in range(runs):
        path = rng.choice(seeds)
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            spec_runner.stage(path, directory)
            text = mutate(path.read_text(), rng)
            (directory / path.name).write_text(text)
            if rng.random() < 0.25:
                cfg = directory / (path.stem + ".cfg")
                if cfg.exists():
                    cfg.write_text(mutate(cfg.read_text(), rng))
            options = spec_runner.options(path)
            if not options and rng.random() < 0.5:
                options = [rng.choice(["-simulate", "-generate"]), "num=5", "-depth", "20", "-seed", str(rng.randint(0, 999))]
            code, out = run(engine, path.stem, directory, 10, options)
            if code is None:
                timeouts += 1
            elif code not in STATUSES or "runtime error" in out or "Sanitizer" in out:
                failed += 1
                kept = ROOT / ".obj" / f"crash-{seed}-{i}.tla"
                kept.parent.mkdir(exist_ok=True)
                kept.write_text(text)
                print(f"FAIL {path.relative_to(ROOT)} {' '.join(options)} exit {code}, kept as {kept.relative_to(ROOT)}")
                print(out[-2000:])
    print(f"{runs - failed}/{runs} mutated models ran without crashing ({timeouts} timed out)")
    return failed


class Gen:
    """Random constant expressions of several types, including lazy values, EXCEPT, and error recovery."""

    def __init__(self, rng):
        self.rng = rng
        self.bound = []

    def pick(self, *options):
        return self.rng.choice(options)()

    def int(self, d=0):
        r = self.rng
        leaf = [lambda: str(r.randint(-3, 9))] + [lambda: x for x, t in self.bound if t == "int"][:1]
        if d > 2:
            return r.choice(leaf)()
        n = lambda: self.int(d + 1)
        return self.pick(
            *leaf,
            lambda: f"({n()} + {n()})",
            lambda: f"({n()} - {n()})",
            lambda: f"({n()} * {n()})",
            lambda: f"({n()} \\div {r.randint(1, 4)})",
            lambda: f"({n()} % {r.randint(1, 4)})",
            lambda: f"(-{n()})",
            lambda: f"(IF {self.bool(d + 1)} THEN {n()} ELSE {n()})",
            lambda: f"Cardinality({self.set(d + 1)})",
            lambda: f"Cardinality({self.big(d + 1)})",
            lambda: f"Len({self.seq(d + 1)})",
            lambda: f"Head({self.seq(d + 1)})",
            lambda: f"({n()} ^ {r.randint(0, 3)})",
            lambda: self.choose(d, "int"),
            lambda: f"{self.record(d + 1)}.a",
            lambda: f"{self.fcn(d + 1)}[{r.randint(0, 4)}]",
            lambda: self.lazy_fcn(d),
            lambda: f"(LET y == {n()} IN y + {n()})",
            lambda: f"(CASE {self.bool(d + 1)} -> {n()} [] {self.bool(d + 1)} -> {n()} [] OTHER -> {n()})",
            lambda: f"(IF AssertError(\"bad\", [i \\in {{1, 2}} |-> i][0]) THEN {n()} ELSE {n()})",
        )

    def bool(self, d=0):
        r = self.rng
        if d > 2:
            return r.choice(["TRUE", "FALSE", f"({self.int(d)} < {self.int(d)})"])
        b = lambda: self.bool(d + 1)
        return self.pick(
            lambda: r.choice(["TRUE", "FALSE"]),
            lambda: f"({self.int(d + 1)} < {self.int(d + 1)})",
            lambda: f"({self.int(d + 1)} = {self.int(d + 1)})",
            lambda: f"({self.int(d + 1)} \\in {self.set(d + 1)})",
            lambda: f"({self.int(d + 1)} \\in {self.lazy(d + 1)})",
            lambda: f"({self.set(d + 1)} \\subseteq {self.lazy(d + 1)})",
            lambda: f"({self.set(d + 1)} \\subseteq {self.set(d + 1)})",
            lambda: f"(~{b()})",
            lambda: f"({b()} /\\ {b()})",
            lambda: f"({b()} \\/ {b()})",
            lambda: f"({b()} => {b()})",
            lambda: f"({b()} <=> {b()})",
            lambda: self.quantifier(d),
            lambda: f"({self.seq(d + 1)} = {self.seq(d + 1)})",
            lambda: f"({self.fcn(d + 1)} = {self.fcn(d + 1)})",
            lambda: f"({self.fcn(d + 1)} = {self.seq(d + 1)})",
            lambda: f"({self.set(d + 1)} = {self.set(d + 1)})",
            lambda: f"({self.seq(d + 1)} \\in Seq({self.set(d + 1)}))",
            lambda: f"({self.record(d + 1)} = {self.record(d + 1)})",
            lambda: f"({self.record(d + 1)} \\in [a: {self.set(d + 1)}, b: BOOLEAN])",
            lambda: f"({r.choice(STRINGS)} = {r.choice(STRINGS)})",
            lambda: f"IsFiniteSet({self.lazy(d + 1)})",
            lambda: f"IsFiniteSet([{{}} -> {self.lazy(d + 1)}])",
            lambda: f"IsFiniteSet({{}} \\X {self.lazy(d + 1)})",
            lambda: f"(AssertError(\"bad\", <<1>>[2]) /\\ {b()})",
        )

    def bind(self, body):
        name = f"x{len(self.bound)}"
        self.bound.append((name, "int"))
        try:
            return name, body()
        finally:
            self.bound.pop()

    def quantifier(self, d):
        s = self.set(d + 1)
        q = self.rng.choice(["\\A", "\\E"])
        x, p = self.bind(lambda: self.bool(d + 1))
        return f"({q} {x} \\in {s} : {p})"

    def choose(self, d, _):
        s = self.set(d + 1)
        x, p = self.bind(lambda: self.bool(d + 1))
        return f"(CHOOSE {x} \\in {s} : {p})"

    def lazy(self, d):
        """An infinite set of integers, which TLC keeps unevaluated."""
        s = lambda: self.set(d + 1)
        x, p = self.bind(lambda: self.bool(d + 1))
        return self.pick(
            lambda: self.rng.choice(["Nat", "Int"]),
            lambda: f"{{{x} \\in Nat : {p}}}",
            lambda: f"(Nat \\ {s()})",
            lambda: f"({s()} \\cup Int)",
            lambda: f"UNION {{{s()}, Nat}}",
        )

    def lazy_fcn(self, d):
        x, e = self.bind(lambda: self.int(d + 1))
        return f"[{x} \\in {self.rng.choice(['Nat', 'Int'])} |-> {e}][{self.rng.randint(-1, 5)}]"

    def set(self, d=0):
        r = self.rng
        n = lambda: self.int(d + 1)
        if d > 2:
            return r.choice(["{}", f"{{{n()}}}", f"({r.randint(0, 2)}..{r.randint(0, 4)})"])
        s = lambda: self.set(d + 1)
        return self.pick(
            lambda: "{" + ", ".join(n() for _ in range(r.randint(0, 4))) + "}",
            lambda: f"({r.randint(-2, 2)}..{r.randint(-1, 5)})",
            lambda: f"({s()} \\cup {s()})",
            lambda: f"({s()} \\cap {s()})",
            lambda: f"({s()} \\ {s()})",
            lambda: self.filter(d),
            lambda: self.image(d),
            lambda: f"DOMAIN {self.seq(d + 1)}",
            lambda: f"DOMAIN {self.fcn(d + 1)}",
            lambda: f"UNION {{{s()}, {s()}}}",
            lambda: f"({s()} \\cap {self.lazy(d + 1)})",
            lambda: f"({s()} \\ {self.lazy(d + 1)})",
        )

    def small_set(self, d=0):
        r = self.rng
        return r.choice(["{}", f"{{{r.randint(0, 2)}}}", f"({r.randint(0, 1)}..{r.randint(1, 2)})"])

    def big(self, d=0):
        """A set of non-integer values, including mixed V_LAMBDA / tuple / record unions and empty lazy sets."""
        s = lambda: self.set(d + 1)
        sm = lambda: self.small_set(d + 1)
        return self.pick(
            lambda: f"DOMAIN {self.record(d + 1)}",
            lambda: "{" + ", ".join(self.rng.sample(STRINGS, self.rng.randint(0, 3))) + "}",
            lambda: f"SUBSET {sm()}",
            lambda: "SUBSET {}",
            lambda: f"({sm()} \\X {sm()})",
            lambda: f"({{}} \\X {self.lazy(d + 1)})",
            lambda: f"[{sm()} -> {sm()}]",
            lambda: f"[{{}} -> {self.lazy(d + 1)}]",
            lambda: f"[a: {sm()}, b: BOOLEAN]",
            lambda: f"{{{self.seq(d + 1)}, {self.seq(d + 1)}}}",
            lambda: f"({{{self.fcn(d + 1)}}} \\cup {{{self.seq(d + 1)}}})",
            lambda: f"({{{self.fcn(d + 1)}}} \\cup {{{self.fcn(d + 1)}}})",
            lambda: f"({{{self.fcn(d + 1)}}} \\cup {{{self.record(d + 1)}}})",
            lambda: f"{{{s()}, {s()}, {s()}}}",
            lambda: f"{{{self.record(d + 1)}, {self.record(d + 1)}}}",
            lambda: f"{{<<{self.int(d + 1)}, {self.rng.choice(STRINGS)}>>, <<{self.int(d + 1)}, {self.rng.choice(STRINGS)}>>}}",
            lambda: f"{{({self.int(d + 1)} :> {self.int(d + 1)} @@ {self.rng.choice(STRINGS)} :> {self.bool(d + 1)})}}",
        )

    def filter(self, d):
        s = self.set(d + 1)
        x, p = self.bind(lambda: self.bool(d + 1))
        return f"{{{x} \\in {s} : {p}}}"

    def image(self, d):
        s = self.set(d + 1)
        x, e = self.bind(lambda: self.int(d + 1))
        return f"{{{e} : {x} \\in {s}}}"

    def seq(self, d=0):
        r = self.rng
        n = lambda: self.int(d + 1)
        if d > 2:
            return "<<" + ", ".join(n() for _ in range(r.randint(0, 3))) + ">>"
        q = lambda: self.seq(d + 1)
        return self.pick(
            lambda: "<<" + ", ".join(n() for _ in range(r.randint(0, 4))) + ">>",
            lambda: f"Append({q()}, {n()})",
            lambda: f"({q()} \\o {q()})",
            lambda: f"SubSeq({q()}, {r.randint(1, 2)}, {r.randint(0, 3)})",
            lambda: f"Tail({q()})",
            lambda: f"SelectSeq({q()}, LAMBDA v : v > {n()})",
            lambda: f"[{q()} EXCEPT ![{r.randint(0, 4)}] = @ * 2]",
            lambda: f"[{self.fcn(d + 1)} EXCEPT ![{r.randint(0, 4)}] = {n()}]",
            lambda: f"SortSeq({q()}, {r.choice(['<', '>'])})",
        )

    def fcn(self, d=0):
        r = self.rng
        dom = r.choice([f"(1..{r.randint(0, 3)})", "{}", "{0, 2}"])
        x, e = self.bind(lambda: self.int(d + 1))
        base = f"[{x} \\in {dom} |-> {e}]"
        if d >= 2 or r.random() < 0.45:
            return base
        k = r.randint(0, 3)
        return r.choice([
            f"[{base} EXCEPT ![{k}] = {self.int(d + 1)}]",
            f"[{base} EXCEPT ![{k}] = LET y == @ IN y + 1]",
            f"[{base} EXCEPT ![{k}] = Cardinality({{z \\in {{0, 1, 2}} : z = @}})]",
        ])

    def record(self, d=0):
        r = [f"[a |-> {self.int(d + 1)}, b |-> {self.bool(d + 1)}]"]
        if d < 2:
            r.append(f"[{self.record(d + 1)} EXCEPT !.a = {self.int(d + 1)}]")
            r.append(f"[{self.record(d + 1)} EXCEPT !.a = LET y == @ IN y + 1]")
        return self.rng.choice(r)

    def any(self):
        return self.pick(self.int, self.bool, self.set, self.big, self.seq, self.fcn, self.record)


def batch_output(command, exprs):
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        lines = "\n".join(f"ASSUME PrintT({e})" for e in exprs)
        (directory / "F.tla").write_text(
            "---- MODULE F ----\nEXTENDS Integers, Sequences, FiniteSets, TLC, TLCExt\n"
            f"{lines}\n====\n"
        )
        (directory / "F.cfg").write_text("")
        code, out = run(command, "F", directory, 60)
        return spec_runner.normalize(out, directory) + f"exit {code}\n"


# TLC's :> and @@, which print a function, for TLAPS (which has no TLC).
PROVE_HEAD = """EXTENDS Integers, Sequences, FiniteSets, TLAPS
d :> e == [x \\in {d} |-> e]
f @@ g == [x \\in (DOMAIN f) \\cup (DOMAIN g) |-> IF x \\in DOMAIN f THEN f[x] ELSE g[x]]
"""
PROVE_BY = "BY SMTT(3), Zenon, IsaT(20) DEF :>, @@"
NONSTANDARD = re.compile(r"AssertError|SortSeq")   # operators TLAPS and lean/ do not define


def values(engine, exprs):
    """The value the engine prints for each expression, None where it fails."""
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        lines = "".join(f'ASSUME PrintT("@{i}")\nASSUME PrintT({e})\n' for i, e in enumerate(exprs))
        (directory / "F.tla").write_text(f"---- MODULE F ----\nEXTENDS Integers, Sequences, FiniteSets, TLC\n{lines}====\n")
        (directory / "F.cfg").write_text("")
        code, out = run(engine, "F", directory, 60, ["-nowarning"])
    if code != 0:
        return [values(engine, [e])[0] for e in exprs] if len(exprs) > 1 else [None]
    found, current = {}, None
    for line in out.splitlines():
        marker = re.fullmatch(r'"@(\d+)"', line)
        if marker:
            current = int(marker.group(1))
            found[current] = []
        elif current is not None and not line.startswith(("Finished computing", "Model checking")):
            found[current].append(line.strip())
        else:
            current = None
    return [" ".join(found[i]) if found.get(i) else None for i in range(len(exprs))]


def unproved(tlapm, claims):
    """The indices of claims TLAPS does not prove."""
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        lines = "".join(f"THEOREM {c} {PROVE_BY}\n" for c in claims)
        (directory / "P.tla").write_text(f"---- MODULE P ----\n{PROVE_HEAD}{lines}====\n")
        first = 2 + PROVE_HEAD.count("\n")   # the line of the first THEOREM
        _, out, code, killed = spec_runner.guarded([tlapm, "--nofp", "--threads", "2", "P.tla"],
                                                   directory, 60 + 10 * len(claims), MEMORY)
    if killed:
        return set(range(len(claims)))
    if code != 0 and "obligations failed" not in out:
        raise RuntimeError(f"tlapm cannot check\n{lines}{out}")
    failing = {int(m) - first for m in re.findall(r'^File "\./P\.tla", line (\d+), char', out, re.M)}
    return {i for i in failing if 0 <= i < len(claims)}


def standard(rng, n):
    """n random expressions of the standard modules."""
    exprs = []
    while len(exprs) < n:
        e = Gen(rng).any()
        if not NONSTANDARD.search(e):
            exprs.append(e)
    return exprs


def prove(engine, tlapm, runs, seed):
    rng = random.Random(seed)
    failed = proved = 0
    size = 25
    for b in range(0, runs, size):
        exprs = standard(rng, min(size, runs - b))
        pairs = [(e, v) for e, v in zip(exprs, values(engine, exprs)) if v is not None]
        left = unproved(tlapm, [f"({e}) = ({v})" for e, v in pairs])
        proved += len(pairs) - len(left)
        doubted = [pairs[i] for i in sorted(left)]
        wrong = unproved(tlapm, [f"({e}) # ({v})" for e, v in doubted])
        for i, (e, v) in enumerate(doubted):
            if i not in wrong:
                failed += 1
                print(f"FAIL TLAPS proves {e} # {v}, the value manyan prints")
    print(f"{proved}/{runs} random expressions proved equal to manyan's value, {failed} proved unequal")
    return failed


def ref(engine, reference, runs, seed):
    rng = random.Random(seed)
    exprs = standard(rng, runs)
    pairs = [(e, v) for e, v in zip(exprs, values(engine, exprs)) if v is not None]
    done = subprocess.run([reference], input="".join(f"{e}\t{v}\n" for e, v in pairs),
                          stdout=subprocess.PIPE, text=True, timeout=600, check=True)
    answers = done.stdout.splitlines()
    assert len(answers) == len(pairs), done.stdout
    failed = 0
    for (e, v), a in zip(pairs, answers):
        if not a.startswith(("same", "undefined:", "unknown:")):
            failed += 1
            print(f"FAIL {e}\n--- manyan\n{v}\n--- lean/\n{a}")
    same = sum(a == "same" for a in answers)
    print(f"{same}/{runs} random expressions have manyan's value by lean/, {failed} another")
    return failed


def diff_model(rng):
    """Small state-machine specs covering action errors, CONSTANT errors, SYMMETRY+V_LAMBDA, and TLCSet."""
    kind_id = rng.randrange(5)
    if kind_id == 0:
        # Action-level out-of-domain lambda application or EXCEPT (exit 75 vs 255)
        k = rng.choice([0, 1, 2, 3])
        body = rng.choice([
            f"x' = [i \\in {{1, 2}} |-> (i + x) % 3][{k}]",
            f"x' = [[i \\in {{1, 2}} |-> i] EXCEPT ![{k}] = x][1]",
            f"x' = [i \\in {{1, 2}} |-> [j \\in {{1, 2}} |-> i + j]][{k}][1]",
        ])
        return (
            f"---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == {body}\n====\n"
            "INIT Init\nNEXT Next\n"
        )
    if kind_id == 1:
        # CONSTANT evaluation error (tests EvalState / keep_lazy leak into Init/Next/replay)
        bad = rng.choice(["<<1>>[2]", "[i \\in {1} |-> i][0]", "1 \\div 0", "[i \\in {1} |-> 1 \\div 0][1]"])
        return (
            "---- MODULE M ----\nEXTENDS Integers, TLCExt\n"
            f"C == {bad}\nVARIABLE x\n"
            f"Init == x = {rng.choice(['[i \\in {1, 2} |-> i]', 'C'])}\n"
            "Next == x' = x\n====\nINIT Init\nNEXT Next\n"
        )
    if kind_id == 2:
        # SYMMETRY over V_LAMBDA / sets of functions
        val = rng.choice([
            "[p \\in S |-> p]",
            "[p \\in S |-> IF p = a THEN 1 ELSE 0]",
            "{[p \\in S |-> p]}",
            "[[p \\in S |-> 0] EXCEPT ![a] = 1]",
        ])
        return (
            "---- MODULE M ----\nEXTENDS Integers, FiniteSets\nCONSTANT S\nVARIABLE x\n"
            "Sym == Permutations(S)\n"
            f"Init == \\E a \\in S : x = {val}\n"
            "Next == x' = x\n====\n"
            "CONSTANT S = {s1, s2}\nSYMMETRY Sym\nINIT Init\nNEXT Next\n"
        )
    if kind_id == 3:
        # Nested EXCEPT with @ in Init/Next + invariant
        return (
            "---- MODULE M ----\nEXTENDS Integers\nVARIABLE f\n"
            "Init == f = [i \\in {1, 2} |-> [j \\in {1, 2} |-> i + j]]\n"
            f"Next == f' = [f EXCEPT ![{rng.choice([1, 2])}] = LET old == @ IN [old EXCEPT ![{rng.choice([1, 2])}] = (@ + 1) % 3]]\n"
            "Inv == f[1][1] < 3\n====\nINIT Init\nNEXT Next\nINVARIANT Inv\n"
        )
    # TLCSet/TLCGet register across states (also checks workers=4 fallback)
    return (
        "---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\n"
        "Init == x = 0 /\\ TLCSet(1, 0)\n"
        "Next == x < 3 /\\ x' = x + 1 /\\ TLCSet(1, TLCGet(1) + 1)\n"
        "Inv == x <= 3\n====\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n"
    )


def diff(engine, tlc, runs, seed):
    rng = random.Random(seed)
    tlc_cmd = tlc.split() + ["-workers", "1"]
    failed = 0
    size = 25
    for b in range(0, runs, size):
        exprs = [Gen(rng).any() for _ in range(min(size, runs - b))]
        meta = ["-metadir", spec_runner.metadir()]
        if batch_output(engine, exprs) == batch_output(tlc_cmd + meta, exprs):
            continue
        for e in exprs:
            meta = ["-metadir", spec_runner.metadir()]
            mine, theirs = batch_output(engine, [e]), batch_output(tlc_cmd + meta, [e])
            if mine != theirs:
                failed += 1
                print(f"FAIL {e}\n--- manyan\n{mine}--- TLC\n{theirs}")
                break
    model_runs = max(10, runs // 10)
    for _ in range(model_runs):
        model = diff_model(rng)
        workers = rng.choice([[], ["-workers", "4"]])
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "M.tla"
            path.write_text(model)
            ours = spec_runner.run(engine + workers, path, MEMORY)
            theirs = spec_runner.run(spec_runner.oracle_command(tlc), path, MEMORY)
        if ours != theirs:
            failed += 1
            print(f"FAIL model {' '.join(workers)}\n{model}--- manyan\n{ours}--- TLC\n{theirs}")
    total = runs + model_runs
    print(f"{total - failed}/{total} random expressions & models printed as TLC prints them")
    return failed


def spec_models():
    """The models of tests/spec that run without options."""
    models = sorted((ROOT / "tests/spec").rglob("*.tla"))
    return [p for p in models if ".files" not in str(p) and not spec_runner.options(p)
            and re.search(r"^\s*(INIT|SPECIFICATION)\b", p.read_text(), flags=re.M)]


def sim(engine, tlc, runs, seed):
    rng = random.Random(seed)
    models = spec_models()
    failed = 0
    for _ in range(runs):
        path = rng.choice(models)
        # TLC's worker runs on past an error until stopped: what it then prints, or counts, races.
        num = 1 if re.search(r"Print|PickSuccessor|_POSSIBLE", path.read_text()) else rng.randint(1, 5)
        options = [rng.choice(["-simulate", "-generate"]), f"num={num}", "-depth", str(rng.randint(1, 30)),
                   "-seed", str(rng.randint(0, 999))] + ["-continue"] * (rng.random() < 0.3)
        ours = spec_runner.run(engine + options, path, MEMORY)
        theirs = spec_runner.run(spec_runner.oracle_command(tlc) + options, path, MEMORY)
        if ours != theirs:
            failed += 1
            print(f"DIFF {path.relative_to(ROOT)} {' '.join(options)}\n--- engine\n{ours}--- TLC\n{theirs}")
    print(f"{runs - failed}/{runs} simulations printed what TLC prints")
    return failed


def check(engine, tlc, runs, seed):
    rng = random.Random(seed)
    models = spec_models()
    failed = 0
    for _ in range(runs):
        path = rng.choice(models)
        options = [o for o in ["-deadlock", "-continue", "-difftrace", "-nowarning", "-view"] if rng.random() < 0.4]
        workers = rng.choice([[], ["-workers", "4"]])
        ours = spec_runner.run(engine + workers + options, path, MEMORY)
        theirs = spec_runner.run(spec_runner.oracle_command(tlc) + options, path, MEMORY)
        if ours != theirs:
            failed += 1
            print(f"DIFF {path.relative_to(ROOT)} {' '.join(workers + options)}\n--- engine\n{ours}--- TLC\n{theirs}")
    print(f"{runs - failed}/{runs} checks printed what TLC prints")
    return failed


def nested(rng, atom, depth):
    """A random temporal formula over state predicates, constants, ~, and LET."""
    if depth == 0 or rng.random() < 0.22:
        return f"({atom()})"
    op = rng.choice(["[]", "<>", "~", "LET", "/\\", "\\/", "~>", "=>"])
    if op in ("[]", "<>", "~"):
        return f"({op}{nested(rng, atom, depth - 1)})"
    if op == "LET":
        return f"(LET q{depth} == {nested(rng, atom, depth - 1)} IN q{depth})"
    return f"({nested(rng, atom, depth - 1)} {op} {nested(rng, atom, depth - 1)})"


def live_model(rng):
    """A random state graph under random fairness, with a rich temporal property."""
    n = rng.randint(2, 5)
    sets = lambda xs: "{" + ", ".join(map(str, sorted(xs))) + "}"
    some = lambda p: {m for m in range(1, n + 1) if rng.random() < p}
    succ = [some(0.4) for _ in range(n)]
    sub = rng.choice(["s", "s", "<<s>>", "TRUE", "FALSE", "BOOLEAN", "STRING"])
    actions, spec = "", f"Init /\\ [][Next]_{sub}"
    for i in range(rng.randint(0, 2)):
        steps = [{k for k in x if rng.random() < 0.5} for x in succ]
        actions += f"A{i} == s' \\in <<{', '.join(sets(x) for x in steps)}>>[s]\n"
        fsub = rng.choice(["s", "s", "TRUE", "FALSE", "BOOLEAN", "STRING"])
        spec += f" /\\ {rng.choice('WS')}F_{fsub}(A{i})"

    def atom():
        return rng.choice([
            f"s \\in {sets(some(0.4))}",
            f"(s * 1) \\in {sets(some(0.4))}",
            f"(s + 0) \\in {sets(some(0.4))}",
            "TRUE",
            "FALSE",
        ])

    x, y = atom(), atom()
    a = f"s' \\in {sets(some(0.4))}"
    psub = rng.choice(["s", "s", "TRUE", "FALSE", "BOOLEAN", "STRING"])
    fair_prop = f"{rng.choice('WS')}F_{psub}({a})"
    nested_lt = f"((({atom()}) ~> ({atom()})) ~> ({atom()})) ~> ({atom()})"
    ho_prop = f"[]<>(ENABLED Ap(Id, {a}))"
    prop = rng.choice([
        f"<>({x})",
        f"[]<>({x})",
        f"<>[]({x})",
        f"({x}) ~> ({y})",
        f"[]({x})",
        f"[]<><<{a}>>_{psub}",
        f"<>[][{a}]_{psub}",
        fair_prop,
        f"[]{fair_prop}",
        f"<>{fair_prop}",
        f"~({fair_prop})",
        f"LET P0 == {nested(rng, atom, 3)} IN P0",
        ho_prop,
        nested_lt,
        nested(rng, atom, rng.randint(3, 5)),
    ])
    extra_files = {}
    extra_defs = "Id(v) == v\nAp(Op(_), v) == Op(v)\n"
    if rng.random() < 0.12:
        # Two INSTANCEs with identical literal names (catches c.inst bugs in tableau)
        extra_files["SubL.tla"] = "---- MODULE SubL ----\nVARIABLE v\nQ == v = 1\nP == <>Q\n====\n"
        extra_defs += "I1 == INSTANCE SubL WITH v <- s\nI2 == INSTANCE SubL WITH v <- (IF s = 1 THEN 2 ELSE 1)\n"
        prop = rng.choice(["I1!P /\\ I2!P", "I1!P ~> I2!P", "~(I1!P /\\ ~I2!P)"])
    model = (
        f"---- MODULE L ----\nEXTENDS Naturals\nVARIABLE s\n"
        f"{extra_defs}"
        f"Succ == <<{', '.join(sets(x) for x in succ)}>>\n"
        f"Init == s \\in {sets(some(0.5) or {1})}\nNext == s' \\in Succ[s]\n{actions}"
        f"Spec == {spec}\nP == {prop}\n====\n"
        "SPECIFICATION Spec\nPROPERTY P\nCHECK_DEADLOCK FALSE\n"
    )
    return model, extra_files


def live(engine, tlc, runs, seed):
    rng = random.Random(seed)
    failed = 0
    for _ in range(runs):
        model, extra_files = live_model(rng)
        fp = ["-fp", str(rng.randrange(131))]   # which orders a state's successors
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            path = directory / "L.tla"
            path.write_text(model)
            if extra_files:
                fdir = path.with_suffix(".files")
                fdir.mkdir()
                for fname, ftext in extra_files.items():
                    (fdir / fname).write_text(ftext)
            ours = spec_runner.run(engine + fp, path, MEMORY)
            theirs = spec_runner.run(spec_runner.oracle_command(tlc) + fp, path, MEMORY)
        if ours != theirs:
            failed += 1
            print(f"DIFF {' '.join(fp)}\n{model}--- engine\n{ours}--- TLC\n{theirs}")
    print(f"{runs - failed}/{runs} liveness checks printed what TLC prints")
    return failed


def fuzz_fmt(engine, runs, seed, sany=None):
    import fmt_runner
    rng = random.Random(seed)
    sany_cmd = shlex.split(sany) if sany else None
    seeds = sorted(
        list((ROOT / "tests/fmt").glob("*.tla"))
        + list((ROOT / "tests/lint").glob("*.tla"))
        + [p for p in (ROOT / "tests/spec").rglob("*.tla") if p.suffixes == [".tla"] and ".files" not in str(p)]
    )
    failed = 0
    for i in range(runs):
        path = rng.choice(seeds)
        text = mutate(path.read_text(), rng)
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            spec_runner.stage(path, directory)
            (directory / path.name).write_text(text)
            try:
                done = subprocess.run(engine + ["-fmt", path.name], cwd=directory, timeout=10,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace")
            except subprocess.TimeoutExpired:
                failed += 1
                kept = ROOT / ".obj" / f"crash-fmt-{seed}-{i}.tla"
                kept.parent.mkdir(exist_ok=True)
                kept.write_text(text)
                print(f"FAIL fmt {path.relative_to(ROOT)} (timeout), kept as {kept.relative_to(ROOT)}")
                continue
            code, raw = done.returncode, done.stdout
            out = fmt_runner.strip_noise(raw)
            bad = code not in (0, 150) or "runtime error" in raw or "Sanitizer" in raw
            reason = f"exit {code}"
            if not bad and code == 0:
                if fmt_runner.extract_comments(text) != fmt_runner.extract_comments(out):
                    bad, reason = True, "comments changed"
                else:
                    orig_sany_ok = False
                    if sany_cmd:
                        _, _, sc0, sk0 = spec_runner.guarded(sany_cmd + ["-error-codes", path.name], directory, 30, MEMORY, b"")
                        orig_sany_ok = not sk0 and sc0 == 0
                    (directory / path.name).write_text(out)
                    try:
                        done2 = subprocess.run(engine + ["-fmt", path.name], cwd=directory, timeout=10,
                                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace")
                    except subprocess.TimeoutExpired:
                        bad, reason = True, "timeout on second format"
                    else:
                        out2 = fmt_runner.strip_noise(done2.stdout)
                        if done2.returncode != 0 or out2 != out:
                            bad, reason = True, f"not idempotent (exit {done2.returncode})"
                        elif orig_sany_ok:
                            _, sout, sc1, sk1 = spec_runner.guarded(sany_cmd + ["-error-codes", path.name], directory, 30, MEMORY, b"")
                            if sk1 or sc1 != 0:
                                bad, reason = True, f"formatted output failed SANY ({sk1 or sc1})"
                                raw = sout
            if bad:
                failed += 1
                kept = ROOT / ".obj" / f"crash-fmt-{seed}-{i}.tla"
                kept.parent.mkdir(exist_ok=True)
                kept.write_text(text)
                print(f"FAIL fmt {path.relative_to(ROOT)} ({reason}), kept as {kept.relative_to(ROOT)}")
                print(raw[-1000:])
    print(f"{runs - failed}/{runs} mutated modules formatted cleanly")
    return failed


def lint_case(rng):
    """Generate a tricky TLA+ module exercising SANY grammar, labels, subscripts, INSTANCE, and levels."""
    kind_id = rng.randrange(7)
    if kind_id == 0:
        sub = rng.choice(["TRUE", "FALSE", "BOOLEAN", "STRING", "x", "<<x>>", "1", "{x}"])
        form = rng.choice([f"[x' = x]_{sub}", f"<<x' = x>>_{sub}", f"WF_{sub}(x' = x)", f"SF_{sub}(x' = x)"])
        return f"---- MODULE T ----\nVARIABLE x\nP == {form}\n====\n", {}
    if kind_id == 1:
        q = rng.choice(["\\A", "\\E"])
        lbl = rng.choice(["l :: {2}", "l(a) :: {2}", "l(a, b) :: {2}"])
        return f"---- MODULE T ----\nP == {q} a \\in {{1}}, b \\in ({lbl}) : a = b\n====\n", {}
    if kind_id == 2:
        rhs = rng.choice(["TRUE", "FALSE", "BOOLEAN", "STRING", "x", "x'", "1 + 2"])
        return (
            "---- MODULE T ----\nEXTENDS Naturals\nVARIABLE x\n"
            f"I == INSTANCE Sub WITH c <- {rhs}\nP == I!Q\n====\n",
            {"Sub.tla": "---- MODULE Sub ----\nCONSTANT c\nQ == c\n====\n"},
        )
    if kind_id == 3:
        body = rng.choice(["1", "x", "x'", "[]x"])
        unused = rng.choice(["1", "x", "x'", "[]x"])
        ctx = rng.choice(["x' = x /\\ P", "(P)'", "[]P"])
        return f"---- MODULE T ----\nVARIABLE x\nP == LET u == {unused} IN {body}\nQ == {ctx}\n====\n", {}
    if kind_id == 4:
        # Set filter vs set enumeration with comma
        expr = rng.choice([
            "{a \\in {1, 2} : a = 1}",
            "{a \\in {1, 2}, TRUE}",
            "{a \\in {1, 2}, b \\in {1, 2} : a = b}",
        ])
        return f"---- MODULE T ----\nP == {expr}\n====\n", {}
    if kind_id == 5:
        # Forward RECURSIVE + temporal / higher-order level check
        return (
            "---- MODULE T ----\nEXTENDS Naturals\nVARIABLE x\n"
            "RECURSIVE R(_)\n"
            f"P == [](R({rng.choice(['1', 'x'])}) = 0)\n"
            "R(n) == IF n = 0 THEN 0 ELSE R(n - 1)\n====\n",
            {},
        )
    # Higher-order operator level propagation
    ctx = rng.choice(["Op(v)", "(Op(v))'", "ENABLED Op(v)", "[]Op(v)"])
    actual = rng.choice(["1", "x", "x'"])
    fbody = rng.choice(["a", "a'", "ENABLED a"])
    return (
        "---- MODULE T ----\nVARIABLE x\n"
        f"F(a) == {fbody}\n"
        f"Ap(Op(_), v) == {ctx}\n"
        f"P == Ap(F, {actual})\n====\n",
        {},
    )


def fuzz_lint(engine, runs, seed, sany=None):
    import lint_runner
    rng = random.Random(seed)
    sany_cmd = shlex.split(sany) if sany else None
    seeds = sorted(
        list((ROOT / "tests/lint").glob("*.tla"))
        + [p for p in (ROOT / "tests/spec").rglob("*.tla") if p.suffixes == [".tla"] and ".files" not in str(p)]
    )
    failed = 0
    for i in range(runs):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            if sany_cmd and i % 2 == 1:
                text, extra = lint_case(rng)
                name = "T.tla"
                mod = directory / name
                mod.write_text(text)
                if extra:
                    fdir = mod.with_suffix(".files")
                    fdir.mkdir()
                    for fname, ftext in extra.items():
                        (fdir / fname).write_text(ftext)
                label = f"generated-{i}"
            else:
                path = rng.choice(seeds)
                text = mutate(path.read_text(), rng)
                name = path.name
                mod = directory / name
                mod.write_text(text)
                files = path.with_suffix(".files")
                if files.is_dir():
                    import shutil
                    shutil.copytree(files, mod.with_suffix(".files"))
                label = str(path.relative_to(ROOT))
            if sany_cmd:
                ours, out = lint_runner.run(engine, mod, False, MEMORY)
                theirs, sout = lint_runner.run(sany_cmd, mod, True, MEMORY)
                bad = ours != theirs or "runtime error" in out or "Sanitizer" in out
                if bad:
                    failed += 1
                    kept = ROOT / ".obj" / f"diff-lint-{seed}-{i}.tla"
                    kept.parent.mkdir(exist_ok=True)
                    kept.write_text(text)
                    print(f"DIFF lint {label}, kept as {kept.relative_to(ROOT)}\n--- manyan\n{ours}--- SANY\n{theirs}")
            else:
                run_dir = directory / "run"
                run_dir.mkdir()
                spec_runner.stage(mod, run_dir)
                try:
                    done = subprocess.run(engine + ["-lint", mod.stem], cwd=run_dir, timeout=10,
                                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace")
                except subprocess.TimeoutExpired:
                    failed += 1
                    kept = ROOT / ".obj" / f"crash-lint-{seed}-{i}.tla"
                    kept.parent.mkdir(exist_ok=True)
                    kept.write_text(text)
                    print(f"FAIL lint {label} timeout, kept as {kept.relative_to(ROOT)}")
                    continue
                code, out = done.returncode, done.stdout
                if code not in (0, 150) or "runtime error" in out or "Sanitizer" in out:
                    failed += 1
                    kept = ROOT / ".obj" / f"crash-lint-{seed}-{i}.tla"
                    kept.parent.mkdir(exist_ok=True)
                    kept.write_text(text)
                    print(f"FAIL lint {label} exit {code}, kept as {kept.relative_to(ROOT)}")
                    print(out[-1000:])
    verb = "matched SANY" if sany_cmd else "linted without crashing"
    print(f"{runs - failed}/{runs} modules {verb}")
    return failed


def fuzz_typecheck(engine, runs, seed):
    rng = random.Random(seed)
    seeds = sorted(
        list((ROOT / "tests/typecheck").rglob("*.tla"))
        + list((ROOT / "tests/symbolic").rglob("*.tla"))
    )
    seeds = [p for p in seeds if p.suffixes == [".tla"] and ".files" not in str(p)]
    failed = 0
    for i in range(runs):
        path = rng.choice(seeds)
        text = mutate(path.read_text(), rng)
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            spec_runner.stage(path, directory)
            (directory / path.name).write_text(text)
            try:
                done = subprocess.run(engine + ["-typecheck", path.stem], cwd=directory, timeout=10,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace")
            except subprocess.TimeoutExpired:
                failed += 1
                kept = ROOT / ".obj" / f"crash-tc-{seed}-{i}.tla"
                kept.parent.mkdir(exist_ok=True)
                kept.write_text(text)
                print(f"FAIL typecheck {path.relative_to(ROOT)} timeout, kept as {kept.relative_to(ROOT)}")
                continue
            code, out = done.returncode, done.stdout
            if code not in TC_STATUSES or "runtime error" in out or "Sanitizer" in out:
                failed += 1
                kept = ROOT / ".obj" / f"crash-tc-{seed}-{i}.tla"
                kept.parent.mkdir(exist_ok=True)
                kept.write_text(text)
                print(f"FAIL typecheck {path.relative_to(ROOT)} exit {code}, kept as {kept.relative_to(ROOT)}")
                print(out[-1000:])
    print(f"{runs - failed}/{runs} mutated modules typechecked without crashing")
    return failed


def sym_spec(rng):
    """Generate a small typed finite-state spec for differential -symbolic vs explicit checking."""
    mode = rng.choice(["inv", "inv", "deadlock", "live"])
    k = rng.randint(2, 5)
    # Apalache reports deadlock only when every behavior is stuck; keep deadlock specs
    # deterministic so explicit BFS and symbolic BMC agree on the exact deadlock step.
    if mode == "deadlock":
        init_x, init_b, init_s, init_f = "x = 0", "b = FALSE", "s = {}", "f = [i \\in {0, 1} |-> 0]"
        x_next = rng.choice([
            "x' = ((x + 1) % 4)",
            "x' = (IF b THEN (x + 1) % 3 ELSE (x + 1) % 4)",
            "x' = (CASE x = 0 -> 1 [] x = 1 -> 2 [] OTHER -> 3)",
            "x' = (LET d == IF 0 \\in s THEN 1 ELSE 1 IN (x + d) % 4)",
        ])
    else:
        init_x = rng.choice(["x \\in 0..2", "x = 0", "x \\in {0, 1}"])
        init_b = rng.choice(["b \\in BOOLEAN", "b = FALSE", "b = TRUE"])
        init_s = rng.choice(["s = {}", "s = {0}", "s \\in SUBSET {0, 1}"])
        init_f = rng.choice(["f = [i \\in {0, 1} |-> 0]", "f = [i \\in {0, 1} |-> i]"])
        x_next = rng.choice([
            "x' = ((x + 1) % 4)",
            "x' = (IF b THEN (x + 1) % 3 ELSE x)",
            "x' = (CASE x = 0 -> 1 [] x = 1 -> 2 [] OTHER -> 0)",
            "x' = (CHOOSE y \\in {0, 1, 2} : y >= x \\/ y = 0)",
            "x' = (LET d == IF 0 \\in s THEN 1 ELSE 2 IN (x + d) % 4)",
            "x' \\in {y \\in 0..3 : y = x \\/ y = (x + 1) % 4}",
            "x' = (f[x % 2] + 1)",
        ])
    b_next = rng.choice([
        "b' = (~b)",
        "b' = (x \\in s)",
        "b' = (\\E y \\in s : y = x)",
        "b' = (\\A y \\in s : y < 2)",
        "b' = (f[0] = f[1])",
    ])
    s_next = rng.choice([
        "s' = (s \\cup {x % 2})",
        "s' = (s \\ {x % 2})",
        "s' = (IF b THEN {0, 1} \\ s ELSE s)",
        "s' = s",
    ])
    f_next = rng.choice([
        "f' = [f EXCEPT ![x % 2] = (x + 1) % 3]",
        "f' = [f EXCEPT ![0] = IF b THEN 1 ELSE 2]",
        "f' = f",
    ])
    guard = rng.choice(["TRUE", "(x < 3)", "(x < 2 \\/ b)", "(~(x = 2 /\\ b))"]) if mode == "deadlock" else "TRUE"
    inv = rng.choice([
        "x < 3",
        "~(x = 2 /\\ b)",
        "f[0] + f[1] < 3",
        "~(0 \\in s /\\ 1 \\in s /\\ b)",
        "x < 4",
    ])
    prop = rng.choice([
        "<>(x = 2)",
        "[](x < 3)",
        "(x = 0) ~> (x = 2)",
        "[]<>(b)",
    ])
    fair = " /\\ WF_<<x, b, s, f>>(Next)" if mode == "live" and rng.random() < 0.5 else ""
    body = (
        "---- MODULE S ----\nEXTENDS Integers, FiniteSets\n"
        "VARIABLES\n"
        "  \\* @type: Int;\n  x,\n"
        "  \\* @type: Bool;\n  b,\n"
        "  \\* @type: Set(Int);\n  s,\n"
        "  \\* @type: Int -> Int;\n  f\n"
        f"Init == {init_x} /\\ {init_b} /\\ {init_s} /\\ {init_f}\n"
        f"Next == {guard} /\\ {x_next} /\\ {b_next} /\\ {s_next} /\\ {f_next}\n"
        f"Spec == Init /\\ [][Next]_<<x, b, s, f>>{fair}\n"
        f"Inv == {inv}\n"
        f"Prop == {prop}\n====\n"
    )
    if mode == "inv":
        cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n"
    elif mode == "deadlock":
        cfg = "INIT Init\nNEXT Next\n"
    else:
        cfg = "SPECIFICATION Spec\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n"
    return mode, k, body + cfg


def explicit_summary(out, code):
    states = len(re.findall(r"^State \d+:", out, flags=re.M))
    if code == 0 and "No error has been found" in out:
        return "ok", 0
    if code == 12 and "is violated" in out:
        return "inv", states or 1
    if code == 11 and "Deadlock reached" in out:
        return "deadlock", states or 1
    if code == 13 and "was violated" in out:
        return "live", states or 1
    return f"other({code})", states


def sym_summary(out, code):
    states = len(re.findall(r"^State \d+:", out, flags=re.M))
    if code == 0 and "No error has been found" in out:
        return "ok", 0
    if code == 12 and "is violated" in out:
        return "inv", states or 1
    if code == 11 and "Deadlock reached" in out:
        return "deadlock", states or 1
    if code == 13 and "was violated" in out:
        return "live", states or 1
    return f"other({code})", states


def fuzz_sym(engine, runs, seed):
    rng = random.Random(seed)
    failed = 0
    for i in range(runs):
        mode, k, text = sym_spec(rng)
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory / "S.tla").write_text(text)
            ends = list(re.finditer(r"^====+[ \t]*$", text, flags=re.M))
            (directory / "S.cfg").write_text(text[ends[-1].end():].lstrip("\n") if ends else "")
            _, eout, ecode, ekilled = spec_runner.guarded(engine + ["-config", "S.cfg", "S"], directory, 30, MEMORY, b"")
            sargs = engine + ["-symbolic", "-length", str(k)] + (["-deadlock"] if mode != "deadlock" else []) + ["-config", "S.cfg", "S"]
            _, sout, scode, skilled = spec_runner.guarded(sargs, directory, 30, MEMORY, b"")
        if ekilled or skilled or "runtime error" in sout or "Sanitizer" in sout or "This is a bug" in sout:
            failed += 1
            print(f"FAIL sym#{i} (killed={ekilled}/{skilled} ecode={ecode} scode={scode})\n{text}\n--- sym\n{sout[-1000:]}")
            continue
        ekind, elen = explicit_summary(eout, ecode)
        skind, slen = sym_summary(sout, scode)
        mismatch = False
        if mode in ("inv", "deadlock"):
            expected_kind = ekind if (ekind != "ok" and elen <= k + 1) else "ok"
            if skind != expected_kind or (expected_kind != "ok" and slen != elen):
                mismatch = True
        else:
            # For temporal properties: no false positives, and if explicit fails on a tiny graph with k >= 5 no bogus error.
            if skind not in ("ok", "live") or (ekind == "ok" and skind == "live"):
                mismatch = True
        if mismatch:
            failed += 1
            print(f"DIFF sym#{i} mode={mode} k={k}: explicit=({ekind},{elen}) symbolic=({skind},{slen})\n{text}\n--- explicit\n{eout[-800:]}\n--- symbolic\n{sout[-800:]}")
    print(f"{runs - failed}/{runs} symbolic checks agreed with explicit engine")
    return failed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["crash", "fmt", "lint", "typecheck", "sym", "diff", "sim", "check", "live", "prove", "ref"])
    parser.add_argument("engine")
    parser.add_argument("--tlc")
    parser.add_argument("--sany")
    parser.add_argument("--tlapm")
    parser.add_argument("--ref")
    parser.add_argument("--runs", type=int, default=200)
    parser.add_argument("--seed", type=int, default=1)
    args = parser.parse_args()
    engine = [str(Path(args.engine).resolve())]
    if args.mode == "crash":
        return 1 if crash(engine, args.runs, args.seed) else 0
    if args.mode == "fmt":
        return 1 if fuzz_fmt(engine, args.runs, args.seed, args.sany) else 0
    if args.mode == "lint":
        return 1 if fuzz_lint(engine, args.runs, args.seed, args.sany) else 0
    if args.mode == "typecheck":
        return 1 if fuzz_typecheck(engine, args.runs, args.seed) else 0
    if args.mode == "sym":
        return 1 if fuzz_sym(engine, args.runs, args.seed) else 0
    if args.mode == "prove":
        if not args.tlapm:
            parser.error("prove needs --tlapm")
        return 1 if prove(engine, str(Path(args.tlapm).resolve()), args.runs, args.seed) else 0
    if args.mode == "ref":
        if not args.ref:
            parser.error("ref needs --ref")
        return 1 if ref(engine, str(Path(args.ref).resolve()), args.runs, args.seed) else 0
    if not args.tlc:
        parser.error(args.mode + " needs --tlc")
    return 1 if {"sim": sim, "check": check, "live": live, "diff": diff}[args.mode](engine, args.tlc, args.runs, args.seed) else 0


if __name__ == "__main__":
    sys.exit(main())
