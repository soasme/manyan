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
the engine and with TLC; they must print the same (but see live).

check: checks models of tests/spec with random options (-deadlock,
-continue, -difftrace, -nowarning, -view), the engine with one or four
workers, and with TLC; they must print the same (but see live).

live: checks a random temporal property (including constants, ~, LET,
nested WF/SF, keyword subscripts, level-0 overrides, higher-order
actions, INSTANCE, and nested ~>) of a random state graph under random
fairness with the engine and with TLC, both with the same random
fingerprint polynomial (-fp); they must print the same, but for a cycle
back into its first state, which TLC prints stuttering and the engine
`Back to state i` (docs/standards/tla2.md §10.5).

prove: makes random constant expressions, evaluates each with the engine,
and asks TLAPS (--tlapm) to prove that the expression equals the value
printed, or else that it does not. A proof of the negation is a finding:
the engine's value contradicts TLA+'s semantics, whatever TLC prints.
What TLAPS proves neither way is inconclusive and left out.

ref: makes the expressions of prove and asks REF, the reference semantics
of lean/, whether each equals the value the engine prints. Another value
is a finding; an expression whose value TLA+ leaves unspecified, or the
reference cannot compute, is left out. The reference also compares each
expression with twins written otherwise, its sets kept unevaluated or
its functions recursive: where both have a value, it is one.

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
            lambda: "({}{}[{}])".format(*self.recursive(d, self.rng.choice(["0..4", "Nat"])), r.randint(-1, 5)),
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
            lambda: f"([a |-> {self.seq(d + 1)}] \\in [a : Seq({self.set(d + 1)})])",
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

    def recursive(self, d, dom):
        """A function on dom that applies itself: the LET that defines it, and its name."""
        g = f"g{len(self.bound)}"
        x, step = self.bind(lambda: self.int(d + 1))
        return f"LET {g}[{x} \\in {dom}] == IF {x} <= 1 THEN {self.int(d + 1)} ELSE {g}[{x} - 1] + {step} IN ", g

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
            lambda: "({}{})".format(*self.recursive(d, f"1..{r.randint(0, 3)}")),
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


class Unevaluated(Gen):
    """Gen's expressions, with each set kept unevaluated: the same value written otherwise."""

    def set(self, d=0):
        return f"({super().set(d)} \\cup {{u \\in Nat : FALSE}})"


class Recursive(Gen):
    """Gen's expressions, with each function and sequence a recursive function."""

    def fcn(self, d=0):
        return self.recursive_twin(super().fcn(d))

    def seq(self, d=0):
        return self.recursive_twin(super().seq(d))

    @staticmethod
    def recursive_twin(f):
        return f"(LET h[k \\in DOMAIN {f}] == {f}[k] IN h)"


def standard(rng, n, gen=Gen):
    """n random expressions of the standard modules."""
    exprs = []
    while len(exprs) < n:
        e = gen(rng).any()
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
    # A function TLC cannot evaluate prints with its body's place: no value.
    pairs = [(e, v) for e, v in zip(exprs, values(engine, exprs)) if v is not None and "<expression" not in v]
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
    # An expression's value cannot depend on how its values are written.
    for gen in Unevaluated, Recursive:
        twins = standard(random.Random(seed), runs, gen)
        done = subprocess.run([reference], input="".join(f"{t}\t{e}\n" for t, e in zip(twins, exprs)),
                              stdout=subprocess.PIPE, text=True, timeout=600, check=True)
        answers = done.stdout.splitlines()
        assert len(answers) == runs, done.stdout
        wrong = [(t, a) for t, a in zip(twins, answers) if not a.startswith(("same", "undefined:", "unknown:"))]
        for t, a in wrong:
            print(f"FAIL {t}\n--- lean/, written as {gen.__name__}\n{a}")
        same = sum(a == "same" for a in answers)
        print(f"{same}/{runs} have that value by lean/ written as {gen.__name__}, {len(wrong)} another")
        failed += len(wrong)
    return failed


class Machine:
    """A random state machine over bounded types, its universe their product."""

    TYPES = ["int", "int", "bool", "set", "fcn", "rec", "seq", "proc"]

    APALACHE = {"int": "Int", "bool": "Bool", "set": "Set(Int)", "fcn": "Int -> Int",
                "rec": "{a: Int, b: Bool}", "seq": "Seq(Int)"}

    def __init__(self, rng, symbolic=False):
        """symbolic: typed for Apalache, and without what -symbolic refuses (RECURSIVE, model values)."""
        self.rng = rng
        self.symbolic = symbolic
        names = ["x", "y", "z"][:rng.randint(1, 3)]
        types = [t for t in self.TYPES if t != "proc"] if symbolic else self.TYPES
        self.vars = {v: rng.choice(types) for v in names}
        self.k = {v: rng.randint(2, 3) for v in names}
        self.constant = False   # no variables, as in Init
        self.lets = 0
        self.actions = []       # those an ENABLED may name

    def domain(self, v):
        return {"int": f"0..{self.k[v] - 1}", "bool": "BOOLEAN", "set": "SUBSET {1, 2}",
                "fcn": "[{1, 2} -> 0..1]", "rec": "[a : 0..1, b : BOOLEAN]",
                "seq": "{<<>>, <<1>>, <<2>>, <<1, 1>>, <<1, 2>>, <<2, 1>>, <<2, 2>>}", "proc": "Procs"}[self.vars[v]]

    def of(self, t):
        return [] if self.constant else [v for v, u in self.vars.items() if u == t]

    def int(self, k, d=0):
        r = self.rng
        leaves = [lambda: str(r.randrange(k))] + [lambda v=v: v for v in self.of("int")]
        leaves += [lambda v=v: f"Cardinality({v})" for v in self.of("set")]
        leaves += [lambda v=v: f"{v}[{r.randint(1, 2)}]" for v in self.of("fcn")]
        leaves += [lambda v=v: f"{v}.a" for v in self.of("rec")]
        leaves += [lambda v=v: f"Len({v})" for v in self.of("seq")]
        leaves += [lambda v=v: f"(IF Len({v}) = 0 THEN 0 ELSE Head({v}))" for v in self.of("seq")]
        leaves += [lambda v=v: f"Sum({v})" for v in ([] if self.symbolic else self.of("set"))]
        leaves += [lambda: "Lim"]
        if d > 2:
            return f"({r.choice(leaves)()} % {k})"
        n = lambda: self.int(k, d + 1)
        return r.choice(leaves + [
            lambda: f"(({n()} + {n()}) % {k})",
            lambda: f"(({n()} * {n()} + 1) % {k})",
            lambda: f"(IF {self.bool(d + 1)} THEN {n()} ELSE {n()})",
            lambda: f"(CASE {self.bool(d + 1)} -> {n()} [] OTHER -> {n()})",
            lambda: self.let(n(), k),
            lambda: self.bound("(CHOOSE {j} \\in 0..{} : {j} = {})", k - 1, n()),
        ])() if d else f"({r.choice(leaves)()} % {k})" if r.random() < 0.3 else r.choice([
            lambda: f"(({n()} + {n()}) % {k})",
            lambda: f"(IF {self.bool(d + 1)} THEN {n()} ELSE {n()})",
            lambda: f"(({n()} + 1) % {k})",
        ])()

    def bound(self, form, *parts):
        """form with parts, {j} a fresh bound name: nested binders may not share one."""
        self.lets += 1
        return form.format(*parts, j=f"j{self.lets}")

    def let(self, e, k):
        return self.bound("(LET w{j} == {} IN (w{j} + 1) % {})", e, k)

    def bool(self, d=0):
        r = self.rng
        leaves = [lambda: r.choice(["TRUE", "FALSE"])] + [lambda v=v: v for v in self.of("bool")]
        leaves += [lambda v=v: f"{v}.b" for v in self.of("rec")]
        leaves += [lambda a=a: f"(ENABLED {a})" for a in ([] if self.constant else self.actions)]
        leaves += [lambda v=v: self.bound("(\\E {j} \\in 1..Len({}) : {}[{j}] = {})", v, v, r.randint(1, 2))
                   for v in self.of("seq")]
        leaves += [lambda v=v, w=w: f"({v} = {w})" for v in self.of("proc") for w in self.of("proc")]
        if d > 2:
            return r.choice(leaves)()
        b = lambda: self.bool(d + 1)
        i = lambda: self.int(3, d + 1)
        return r.choice(leaves + [
            lambda: f"({i()} < {i()})",
            lambda: f"({i()} = {i()})",
            lambda: f"(~{b()})",
            lambda: f"({b()} /\\ {b()})",
            lambda: f"({b()} \\/ {b()})",
            lambda: f"({b()} => {b()})",
            lambda: f"({r.randint(1, 2)} \\in {self.set(d + 1)})",
            lambda: f"({self.set(d + 1)} \\subseteq {self.set(d + 1)})",
            lambda: self.bound("(\\E {j} \\in 0..2 : {j} = {})", i()),
            lambda: self.bound("(\\A {j} \\in {} : {j} > {})", self.set(d + 1), r.randint(0, 2)),
        ] + [lambda v=v: f"({v} = {self.value(v, d + 1)})" for v in self.vars if not self.constant])()

    def set(self, d=0):
        r = self.rng
        empty = "({1} \\ {1})" if self.symbolic else "{}"   # Apalache cannot type {} alone
        leaves = [lambda: r.choice([empty, "{1}", "{2}", "{1, 2}"])] + [lambda v=v: v for v in self.of("set")]
        if d > 2:
            return r.choice(leaves)()
        s = lambda: self.set(d + 1)
        return r.choice(leaves + [
            lambda: f"({s()} \\cup {s()})",
            lambda: f"({s()} \\cap {s()})",
            lambda: f"({s()} \\ {s()})",
            lambda: self.bound("{{{j} \\in {{1, 2}} : {}}}", self.bool(d + 1)),
            lambda: f"({{{self.int(2, d + 1)} + 1}})",
        ])()

    def value(self, v, d=0):
        """An expression of v's type, in its domain."""
        t, r = self.vars[v], self.rng
        if t == "int":
            return f"({self.int(self.k[v], d)} % {self.k[v]})"
        if t == "bool":
            return self.bool(d)
        if t == "set":
            return self.set(d)
        if t == "fcn":
            base = v if r.random() < 0.6 and not self.constant else self.bound("[{j} \\in {{1, 2}} |-> {}]", self.int(2, d + 1))
            return r.choice([base, f"[{base} EXCEPT ![{r.randint(1, 2)}] = {self.int(2, d + 1)}]",
                             f"[{base} EXCEPT ![{r.randint(1, 2)}] = (@ + 1) % 2]"])
        if t == "seq":
            k = r.randint(1, 2)
            nil = "SubSeq(<<1>>, 1, 0)" if self.symbolic else "<<>>"   # Apalache cannot type <<>> alone
            base = nil if self.constant else v
            return r.choice([f"Append({nil}, {k})", nil, f"(IF Len({base}) < 2 THEN Append({base}, {k}) ELSE Tail({base}))",
                             f"(IF Len({base}) = 0 THEN {base} ELSE Tail({base}))",
                             f"(IF Len({base}) = 0 THEN {base} ELSE SubSeq({base}, 1, 1))",
                             f"({base} \\o {nil})", f"(IF Len({base}) = 2 THEN {nil} ELSE Append({base}, {k}))"])
        if t == "proc":
            return v   # which model value CHOOSE picks only TLC knows
        rec = f"[a |-> {self.int(2, d + 1)}, b |-> {self.bool(d + 1)}]"
        if self.constant:
            return rec
        return r.choice([v, rec, f"[{v} EXCEPT !.a = {self.int(2, d + 1)}]", f"[{v} EXCEPT !.b = ~@]"])

    def assign(self, v):
        r = self.rng
        return r.choice([
            lambda: f"{v}' = {self.value(v)}",
            lambda: f"{v}' = {self.value(v)}",
            lambda: f"{v}' \\in {{{self.value(v)}, {self.value(v)}}}",
            lambda: f"UNCHANGED {v}",
            lambda: f"{v}' \\in {self.domain(v)}",
            lambda: f"\\E q \\in {{{self.value(v)}, {self.value(v)}}} : {v}' = q",
            lambda: f"Keep({v})",
            lambda: f"\\E q \\in {self.domain(v)} : {v}' = q",
            lambda: f"(IF {self.bool()} THEN {v}' = {self.value(v)} ELSE {self.assign(v)})",
            lambda: f"(CASE {self.bool()} -> {v}' = {self.value(v)} [] OTHER -> {v}' \\in {self.domain(v)})",
            lambda: f"({v}' = {self.value(v)} \\/ ({self.bool()} /\\ {v}' = {self.value(v)}))",
        ])()

    def action(self):
        r = self.rng
        conj = [self.bool()] if r.random() < 0.7 else []
        vs = list(self.vars)
        if len(vs) > 1 and r.random() < 0.2:
            kept = r.sample(vs, 2)
            conj.append(f"UNCHANGED <<{', '.join(kept)}>>")
            vs = [v for v in vs if v not in kept]
        conj += [self.assign(v) for v in vs]
        r.shuffle(conj)
        # After the assignments, as TLC reads them: a guard on the next state.
        if r.random() < 0.25:
            v = r.choice(list(self.vars))
            conj.append(r.choice([f"{v}' = {self.value(v)}", f"{v}' # {self.value(v)}", f"{v}' = {v}"]))
        return "\n".join("    /\\ " + c for c in conj)

    def model(self):
        r = self.rng
        vs = list(self.vars)
        acts = [f"A{i} ==\n{self.action()}" for i in range(r.randint(1, 3))]
        names = [a.split(" ")[0] for a in acts]
        self.actions = names   # ENABLED in invariants and properties: in a guard, lean/ is cubic
        nxt = "Next ==\n" + "\n".join(f"    \\/ {a}" for a in names)
        self.constant = True
        init = "Init ==\n" + "\n".join(
            "    /\\ " + (f"{v} \\in Procs" if self.vars[v] == "proc" else r.choice([f"{v} = {self.value(v)}", f"{v} \\in {self.domain(v)}",
                                 f"{v} \\in {{{self.value(v)}, {self.value(v)}}}",
                                 f"(\\E q \\in {self.domain(v)} : {v} = q /\\ q # {self.value(v)})"])) for v in vs)
        self.constant = False
        universe = "U == [" + ", ".join(f"{v} : {self.domain(v)}" for v in vs) + "]"
        # Manyan checks the behaviors stay in the universe: lean/ explores no other state.
        props = "TypeOK ==\n" + "\n".join(f"    /\\ {self.typed(v)}" for v in vs) + "\n"
        cfg = ["INVARIANT TypeOK"]
        tuple_ = f"<<{', '.join(vs)}>>"
        if r.random() < 0.4:
            if self.symbolic:
                props += f"\\* @type: <<{', '.join(self.APALACHE[self.vars[v]] for v in vs)}>>;\n"
            fair = " /\\ ".join(f"{r.choice('WS')}F_vars({a})" for a in r.sample(names + ["Next"], r.randint(0, 2)))
            if r.random() < 0.3:
                fair += (" /\\ " if fair else "") + f"(\\A k \\in {{0, 1}} : {r.choice('WS')}F_vars(Step(k)))"
            props += f"vars == {tuple_}\nSpec == Init /\\ [][Next]_vars{' /\\ ' + fair if fair else ''}\n"
            p = r.choice([f"[]{self.bool()}", f"<>{self.bool()}", f"({self.bool()} ~> {self.bool()})",
                          f"[]<>{self.bool()}", f"<>[]{self.bool()}", f"[][{self.action_short()}]_vars",
                          f"[]<><<{r.choice(names)}>>_vars"])
            props += f"Prop == {p}\n"
            cfg += ["SPECIFICATION Spec", "PROPERTY Prop"]
        else:
            cfg += ["INIT Init", "NEXT Next"]
        if r.random() < 0.7:
            props += f"Inv == {self.bool()}\n"
            cfg.append("INVARIANT Inv")
        if r.random() < 0.15:
            props += f"Constr == {self.bool()}\n"
            cfg.append("CONSTRAINT Constr")
        if r.random() < 0.1:
            props += f"AConstr == {self.action_short()}\n"
            cfg.append("ACTION_CONSTRAINT AConstr")
        cfg.append(f"CHECK_DEADLOCK {r.choice(['TRUE', 'FALSE'])}")
        procs = "" if self.symbolic else f"Procs = {r.choice(['{p1}', '{p1, p2}'])} "
        cfg.append(f"CONSTANTS {procs}Lim = {r.randint(0, 1)}")
        if self.symbolic:
            decls = ("CONSTANT\n    \\* @type: Int;\n    Lim\nVARIABLES\n" +
                     ",\n".join(f"    \\* @type: {self.APALACHE[self.vars[v]]};\n    {v}" for v in vs) + "\n")
        else:
            decls = (f"CONSTANTS Procs, Lim\nVARIABLES {', '.join(vs)}\nRECURSIVE Sum(_)\n"
                     f"Sum(S) == IF S = {{}} THEN 0 ELSE LET e == CHOOSE e \\in S : \\A f \\in S : e <= f IN e + Sum(S \\ {{e}})\n")
        module = (f"---- MODULE M ----\nEXTENDS Integers, FiniteSets, Sequences\n{decls}"
                  f"Keep(a) == a' = a\n{init}\n" + "\n".join(acts) + f"\n{nxt}\nStep(k) == IF k = 0 THEN {names[0]} ELSE {names[-1]}\n{universe}\n{props}====\n")
        return module, "\n".join(cfg) + "\n"

    def typed(self, v):
        """That v is in its domain, as Apalache can type it."""
        if self.vars[v] == "seq":
            return self.bound("Len({}) <= 2 /\\ \\A {j} \\in 1..Len({}) : {}[{j}] \\in {{1, 2}}", v, v, v)
        if self.vars[v] == "set":
            return f"{v} \\subseteq {{1, 2}}"
        return f"{v} \\in {self.domain(v)}"

    def action_short(self):
        v = self.rng.choice(list(self.vars))
        return f"{v}' = {self.value(v)} \\/ {self.bool()}"


def live_universe(rng):
    """A model of live_model, with its universe and the modules it uses."""
    module, files = live_model(rng)
    n = re.search(r"Succ == <<(.*)>>", module).group(1).count("{")
    module = module.replace("\n====\n", f"\nU == [s : 1..{n}]\n====\n")
    text, cfg = module.split("====\n")
    return text + "====\n", cfg, files


VERDICT = re.compile(r"^Error: (Invariant (\w+) is violated\.|Deadlock reached\.|Action property (\w+) is violated\.|"
                     r"Temporal propert(?:y (\w+) was|ies (.*) were) violated\.|Assumption .* is false\.)", re.M)


def manyan_trace(out):
    """The states of the behavior Manyan prints, as records, and the state its last goes back to."""
    blocks = re.split(r"^State \d+: ", out, flags=re.M)[1:]
    states, loop = [], None
    for b in blocks:
        head, _, body = b.partition("\n")
        if head.startswith("Stuttering"):
            loop = len(states) - 1
            break
        body = body.split("\n\n")[0]
        back = re.search(r"^Back to state (\d+)", body, re.M)
        body = re.split(r"^(?:Back to state|\d+ states generated)", body, flags=re.M)[0]
        lines = [l for l in body.splitlines() if l.strip()]
        joined, cur = [], ""
        for l in lines:
            if l.startswith("/\\ ") or (not cur and re.match(r"\w+ = ", l)):
                if cur:
                    joined.append(cur)
                cur = l[3:] if l.startswith("/\\ ") else l
            else:
                cur += " " + l.strip()
        if cur:
            joined.append(cur)
        fields = [j.split(" = ", 1) for j in joined]
        states.append("[" + ", ".join(f"{n} |-> {v}" for n, v in fields) + "]")
        if back:
            loop = int(back.group(1)) - 1
            break
    tail = re.search(r"^Back to state (\d+)", out, re.M)
    if loop is None and tail:
        loop = int(tail.group(1)) - 1
    return states, loop


def model_verdict(reference, directory, name, trace=None):
    command = [reference, "model", f"{name}.tla", f"{name}.cfg", "U"] + (["T"] if trace else [])
    if trace:
        (directory / "T").write_text(trace)
    _, out, code, killed = spec_runner.guarded(command, directory, 300, MEMORY)
    if killed:
        return {"skip": f"ref {killed}"}
    if re.match(r"(unknown|undefined|error):", out):
        return {"skip": out.strip()}
    v = {"invariants": {}, "deadlock": None, "properties": {}, "assume": "assume FALSE" in out}
    for line in out.splitlines():
        w = line.split()
        if w[0] in ("states", "init", "depth"):
            v[w[0]] = int(w[1])
        elif w[0] == "invariant":
            v["invariants"][w[1]] = int(w[2])
        elif w[0] == "deadlock":
            v["deadlock"] = int(w[1])
        elif w[0] == "property":
            v["properties"][w[1]] = w[2] == "holds"
        elif w[0] == "trace":
            v["trace"] = w[1] == "valid"
    return v


def judge(out, code, ref, reference, directory, name, cfg, length=None, simulated=False):
    """Why Manyan's verdict is not TLA+'s, or None. length: Manyan checked behaviors of up to that many
    steps; simulated: behaviors drawn at random, so an error may be missed, or found by a longer one."""
    m = VERDICT.search(out)
    states = re.search(r"(\d+) distinct states? found", out)
    depth = re.search(r"The depth of the complete state graph search is (\d+)", out)
    if ref["assume"]:
        return None if m and m.group(0).startswith("Error: Assumption") else "an assumption is FALSE"
    first_inv = min(ref["invariants"].values(), default=None)
    dead = ref["deadlock"]
    # -symbolic reads a deadlock as Apalache does, every behavior stuck, unless the verdict is TLC's.
    apalache = length is not None and not (re.search(r"^(ACTION_)?CONSTRAINT", cfg, re.M) or (
        re.search(r"^PROPERTY", cfg, re.M) and re.search(r"[WS]F_", (directory / f"{name}.tla").read_text())))
    violated = [p for p, h in ref["properties"].items() if not h]
    if m is None:
        if code != 0 or simulated:
            return None   # Manyan refused, as TLC would: not a verdict
        if length is not None:
            within = lambda d: d is not None and d <= length + 1   # a state length steps from an initial one
            # A deadlock lean/ sees may be a step out of the universe, which TypeOK shows a step later.
            if any(map(within, ref["invariants"].values())) or (dead and within(dead + 1) and not apalache):
                return f"no error in behaviors of up to {length} steps, but lean/ has {ref}"
            return None
        if ref["invariants"] or dead or violated:
            return f"no error found, but lean/ has {ref}"
        if not states or int(states.group(1)) != ref["states"]:
            return f"{states and states.group(1)} distinct states, lean/ {ref['states']}"
        if depth and ref["states"] and int(depth.group(1)) != ref["depth"]:   # TLC's is 1 with no state
            return f"depth {depth.group(1)}, lean/ {ref['depth']}"
        return None
    what = m.group(1)
    trace, loop = manyan_trace(out[m.end():])
    if what.startswith("Invariant") and not re.search(rf"^INVARIANT {m.group(2)}$", cfg, re.M):
        what = "Action property"   # TLC reports a violated []P, or a LET's, as an invariant
    if what.startswith("Invariant"):
        inv = m.group(2)
        if inv == "TypeOK":
            return None   # a behavior leaves the universe: lean/ cannot say
        if inv not in ref["invariants"]:
            return f"{inv} violated, but lean/ has it hold"
        if len(trace) < ref["invariants"][inv] or (len(trace) != first_inv and not simulated):
            return f"a trace of {len(trace)} states, lean/ a violation at depth {first_inv}"
        if dead is not None and dead < len(trace) - 1 and not simulated:
            return f"an invariant violated at depth {len(trace)}, but lean/ has a deadlock at {dead}"
        check = f"invariant {inv}"
    elif what.startswith("Deadlock") and simulated and re.search(r"^(ACTION_)?CONSTRAINT", cfg, re.M):
        check = "stuck"   # TLC's simulator stops where no next state is in the constraints
    elif what.startswith("Deadlock"):
        if dead is None:
            return "a deadlock, but lean/ has none"
        if len(trace) != dead and not ((apalache or simulated) and len(trace) > dead):
            return f"a deadlock after {len(trace)} states, lean/ at depth {dead}"
        if first_inv is not None and first_inv <= dead and not simulated:
            return f"a deadlock at depth {dead}, but lean/ has an invariant violated at {first_inv}"
        check = "deadlock"
    elif what.startswith("Assumption"):
        return "an assumption FALSE, but lean/ has them hold"
    else:
        names = [n for n in (m.group(2), m.group(3), m.group(4)) if n] or [n.strip() for n in (m.group(5) or "").split(",") if n.strip()]
        kind = "safety" if what.startswith("Action") else "property"
        # TLC checks a state's invariants and safety properties as it finds it, deadlock as it expands it,
        # and temporal properties once the graph is complete.
        before = len(trace) if kind == "safety" else float("inf")
        if not simulated and ((first_inv or before) < before or (not apalache and (dead or before) < before - 1)):
            return f"a violation of a property, but lean/ has another first: {ref}"
        if not violated:
            return f"{what}, but lean/ has every property hold"
        check = f"{kind} {(set(names) & set(violated) or set(violated)).pop()}"
    text = check + "\n" + "\n".join(trace) + "\n" + (f"loop {loop}\n" if loop is not None and check.startswith("property") else "")
    validated = model_verdict(reference, directory, name, text)
    if validated.get("trace") is not True:
        return f"Manyan's trace is not a behavior that shows it: {validated}\n{text}"
    return None


def models(engine, reference, runs, seed, symbolic=False, simulate=False, keep=None):
    """keep: a directory to copy each failing model into, with the options Manyan ran with."""
    rng = random.Random(seed)
    failed = skipped = refused = slow = 0
    for i in range(runs):
        if symbolic:
            module, cfg, files = Machine(rng, symbolic=True).model() + ({},)
        else:
            module, cfg, files = live_universe(rng) if i % 2 else Machine(rng).model() + ({},)
        name = re.search(r"MODULE (\w+)", module).group(1)
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for f, text in files.items():
                (directory / f).write_text(text)
            (directory / f"{name}.tla").write_text(module)
            (directory / f"{name}.cfg").write_text(cfg)
            ref_v = model_verdict(reference, directory, name)
            if "skip" in ref_v:
                skipped += 1
                continue
            length = rng.randint(1, 8) if symbolic else None
            options = (["-symbolic", "-length", str(length)] if symbolic else
                       ["-simulate", "num=20", "-depth", str(rng.randint(1, 10)), "-seed", str(rng.randrange(1 << 30))]
                       if simulate else ["-workers", "4"] if rng.random() < 0.3 else [])
            _, out, code, killed = spec_runner.guarded(engine + options + ["-config", f"{name}.cfg", name],
                                                       directory, 30 if symbolic else 120, MEMORY)
            if killed and symbolic and killed.endswith(" s"):
                slow += 1   # counted, not failed
                continue
            if killed:
                print(f"FAIL manyan {killed}\n{module}{cfg}")
                failed += 1
                continue
            if code not in (0, 10, 11, 12, 13):
                refused += 1
            why = judge(out, code, ref_v, reference, directory, name, cfg, length, simulate)
        if why:
            failed += 1
            print(f"FAIL {why}\n{module}{cfg}--- manyan {' '.join(options)}\n{out}")
            if keep:
                kept = Path(keep) / f"{seed}-{i}"
                kept.mkdir(parents=True, exist_ok=True)
                for f, text in {f"{name}.tla": module, f"{name}.cfg": cfg, "options": " ".join(options) + "\n", **files}.items():
                    (kept / f).write_text(text)
    print(f"{runs - failed - skipped - slow}/{runs} random models have TLA+'s verdict by lean/, "
          f"{failed} another; {skipped} left out, {refused} refused by manyan" + (f", {slow} too slow" if symbolic else ""))
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
        if ours != back_into(theirs):
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
        if ours != back_into(theirs):
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
    sub = rng.choice(["s", "<<s>>"])   # any other lets s change as it likes
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
        # INSTANCEs with identical literal names (catches c.inst bugs in tableau), one with a parameter
        extra_files["SubL.tla"] = "---- MODULE SubL ----\nVARIABLE v\nQ == v = 1\nR(w) == v = w\nP == <>Q\n====\n"
        extra_defs += ("I1 == INSTANCE SubL WITH v <- s\nI2 == INSTANCE SubL WITH v <- (IF s = 1 THEN 2 ELSE 1)\n"
                       "I3(k) == INSTANCE SubL WITH v <- (IF s = k THEN 1 ELSE 2)\n")
        prop = rng.choice(["I1!P /\\ I2!P", "I1!P ~> I2!P", "~(I1!P /\\ ~I2!P)",
                           "I3(1)!P /\\ I3(2)!P", "[](I3(s)!Q => <>I3(2)!R(1))", "<>[]~I3(3)!R(s)"])
    model = (
        f"---- MODULE L ----\nEXTENDS Naturals\nVARIABLE s\n"
        f"{extra_defs}"
        f"Succ == <<{', '.join(sets(x) for x in succ)}>>\n"
        f"Init == s \\in {sets(some(0.5) or {1})}\nNext == s' \\in Succ[s]\n{actions}"
        f"Spec == {spec}\nP == {prop}\n====\n"
        "SPECIFICATION Spec\nPROPERTY P\nCHECK_DEADLOCK FALSE\n"
    )
    return model, extra_files


def back_into(tlc):
    """TLC's output with a lasso's cycle back into its first state, which
    TLC prints as that state again, then stuttering numbered before it, as
    Manyan prints it: `Back to state i`."""
    m = re.search(r"^State (\d+): (<[^\n]*>)\n((?:[^\n]+\n)+)\nState (\d+): Stuttering\n", tlc, re.M)
    if not m or int(m.group(4)) >= int(m.group(1)):
        return tlc
    first = re.search(r"^State (\d+): [^\n]*\n" + re.escape(m.group(3)) + "\n", tlc[:m.start()], re.M)
    return tlc[:m.start()] + f"Back to state {first.group(1)}: {m.group(2)}\n\n" + tlc[m.end():] if first else tlc


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
        if ours != back_into(theirs):
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
            # As Apalache: k steps reach a state k steps out, and a deadlock there needs a step more.
            reach = k + 1 if ekind == "inv" else k
            expected_kind = ekind if (ekind != "ok" and elen <= reach) else "ok"
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
    parser.add_argument("mode", choices=["crash", "fmt", "lint", "typecheck", "sym", "diff", "sim", "check", "live", "prove", "ref", "model"])
    parser.add_argument("engine")
    parser.add_argument("--tlc")
    parser.add_argument("--sany")
    parser.add_argument("--tlapm")
    parser.add_argument("--ref")
    parser.add_argument("--symbolic", action="store_true", help="model: check with -symbolic")
    parser.add_argument("--simulate", action="store_true", help="model: check with -simulate")
    parser.add_argument("--keep", help="model: a directory to keep failing models in")
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
    if args.mode in ("ref", "model"):
        if not args.ref:
            parser.error(args.mode + " needs --ref")
        reference = str(Path(args.ref).resolve())
        if args.mode == "model":
            return 1 if models(engine, reference, args.runs, args.seed, args.symbolic, args.simulate, args.keep) else 0
        return 1 if ref(engine, reference, args.runs, args.seed) else 0
    if not args.tlc:
        parser.error(args.mode + " needs --tlc")
    return 1 if {"sim": sim, "check": check, "live": live, "diff": diff}[args.mode](engine, args.tlc, args.runs, args.seed) else 0


if __name__ == "__main__":
    sys.exit(main())
