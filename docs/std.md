# Standard modules

TLC computes some operators of its modules in Java instead of from their
TLA⁺ definitions: the operators of its own standard modules and some of
CommunityModules'. Manyan computes them in C. This document lists them and
says how one is written.

## Built in

Naturals, Integers, Reals, Sequences, FiniteSets, TLC, Bags,
Randomization, RealTime, Toolbox, TLCExt and Json are built into `manyan.c`: a
spec need not supply them, and one it supplies is read in their place. Of
TLCExt, `TLCFP` stops the check: its value is TLC's fingerprint, which
changes from run to run ([limitations](manual.md#limitations)).
`PickSuccessor(e)` asks on standard input, as TLC does, whether to take
each step to a state not yet seen where `e` is false: yes (or an empty
line), no, explored (taken, but not expanded), or print the two states or
what changes. At the end of the input Manyan stops, where TLC asks
again while it reports the error.

## CommunityModules

A module of [CommunityModules](https://github.com/tlaplus/CommunityModules)
is read from the spec's directory, as TLC reads it from its class path. Its
operators come from their definitions, except those below: TLC overrides
them in Java from the jar, and Manyan in `manyan-std.c`, giving what that Java
gives, error messages included.

| module | operators |
|---|---|
| BagsExt | `FoldBag` |
| CSV | `CSVWrite`, `CSVWriteRecord`, `CSVRead`, `CSVRecords` (a line too short for `CSVRead`'s columns fails in `CSVRead`, where TLC fails when the record is used) |
| Functions | `FoldFunction`, `FoldFunctionOnSet` |
| Graphs | `SimplePath`, `AreConnectedIn`, `IsStronglyConnected` |
| IOUtils | `IOEnv`, `atoi`, `IOExec`, `IOEnvExec`, `Serialize` (format `TXT`; another format is the definition's) |
| Json | `ToJson`, `ToJsonArray`, `ToJsonObject`, `JsonSerialize`, `ndJsonSerialize`, `JsonDeserialize`, `ndJsonDeserialize` (a record literal in an `ASSUME` is written in TLC's order, where TLC writes it as written) |
| SequencesExt | `SetToSeq`, `FoldSeq`, `SelectInSeq`, `SelectInSubSeq`, `SelectLastInSeq`, `SelectLastInSubSeq`, `IsPrefix` |
| Statistics | `ChiSquare` |
| SVG | `SVGElemToString`, `NodeOfRingNetwork` |
| UndirectedGraphs | `ConnectedComponents` |

## Writing one

A native operator is a C function on the values of `manyan.h`. `manyan_define`
binds it to an operator of every module of that name, when the operator's
definition takes as many arguments, as TLC binds its Java by name. The last
argument is the Java method as TLC names it when the operator fails; Manyan
prints it in the same place. As TLC, Manyan casts each argument to its
parameter's class there, `tlc2.value.impl.StringValue` say, and fails as
Java's cast does on another value.

```c
#include "manyan.h"

/* SequencesExt's SetToSeq(S): S's elements, in TLC's order. */
static ManyanValue *set_to_seq(ManyanCall *call, ManyanValue **a) {
    ManyanValue *s = manyan_elements(a[0]);
    if (!s) manyan_fail(call, "Attempted to enumerate a set that is not enumerable:\n%s", manyan_print(a[0]));
    ManyanValue *elems[manyan_size(s) + 1];
    for (size_t i = 0; i < manyan_size(s); i++) elems[i] = manyan_element(s, i);
    return manyan_tuple(manyan_size(s), elems);
}

manyan_define("SequencesExt", "SetToSeq", 1, set_to_seq,
           "public static tlc2.value.impl.Value tlc2.overrides.SequencesExt.SetToSeq(tlc2.value.impl.Value)");
```

Arguments arrive evaluated. With arity `MANYAN_LAZY` the operator takes any
number of them unevaluated, as TLC's evaluation methods do, and evaluates
each it needs with `manyan_arg`; returning `NULL` then leaves the call to the
definition, as `Serialize` does for a format other than `TXT`.

Values are made and read with the functions `manyan.h` declares. A record is a
function from strings (`manyan_record` makes one TLC's Java makes as a
`RecordValue`), a sequence a tuple, and the elements of sets and the keys
of functions come in TLC's order. Values belong to the evaluation that
made them; a native keeps none past its return. An error does not return:
`manyan_fail` for one TLC's Java raises as an `EvalException`, which TLC
prints as it is, and `manyan_throw` for another exception, which TLC prints
under the Java method that threw it, so memory a native needs across one
comes from `manyan_alloc`, which lives as values do. `manyan_format` is Java's
`String.format` on strings, `manyan_to_string` a value as TLC's
`toString` writes it, on one line, and `manyan_apply` an operator passed as
an argument, as the folds apply theirs.

Each new native gets a test in `tests/spec/stdlib`, its expected output
from TLC with the CommunityModules jar (`make bless`), and a stub of the
module in the test's `.files` directory with the definition TLC overrides.
