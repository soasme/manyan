# manyan

[Manyan](https://github.com/soasme/manyan) is a fast model checker for TLA⁺,
compatible with TLC and Apalache. It is a native executable, with no JVM.

```sh
pip install manyan
manyan -workers auto examples/DieHard
```

The wheel installs the same `manyan` a
[release](https://github.com/soasme/manyan/releases) ships, so it prints and
exits as the release does, with `-workers` too. `python -m manyan` runs it
as well, and `manyan.find_manyan_bin()` gives its path.

`manyan.run(args, cwd=None, stdin=None)` runs it and gives what the check
found as values, with no text to parse:

```python
import manyan

run = manyan.run(["DieHard"], cwd="examples")
run.status                    # 12: an invariant is violated
run.result.violated           # ['NotSolved']
run.result.states[-1]         # {'small': 3, 'big': 4}
run.result.actions[1]["name"] # 'Next'
run.result.loop               # 0: the behavior ends; else the state it steps back to
run.result.distinct           # 14
```

`manyan.check(spec, **options)` does the same in Python's own process,
with the library the wheel installs beside it (not on Windows): its
options are those of `manyan.h`'s `ManyanOptions`, by name, and it gives
what `run` does, with no process started.

```python
run = manyan.check("examples/DieHard", workers=4)
run = manyan.check("Spec", config="Small.cfg", check_deadlock=False, invariants=["x < 10"])
```

`states` holds the first counterexample the report prints whole, each a
record of the variables; `actions` the step into each, as
`TLCGet("action")` gives it, one more stepping back where there is a loop.
A TLA+ value is a boolean, integer or string as itself, a tuple a tuple, a
set a frozenset, a function or record a `manyan.Function` (a dict a set can
hold), and any other, such as a model value, a `manyan.Printed`: a str of
TLC's text of it.

See [the manual](https://github.com/soasme/manyan/blob/main/docs/manual.md).
