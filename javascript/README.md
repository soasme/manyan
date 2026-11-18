# @soasme/manyan

[Manyan](https://github.com/soasme/manyan), a fast model checker for TLA⁺
compatible with TLC and Apalache, compiled to WebAssembly: check a spec in a
web page or in Node.js with nothing else installed.

```sh
npm install @soasme/manyan
```

```js
import { run } from "@soasme/manyan";

const { status, output } = await run(["DieHard"], {
  files: { "DieHard.tla": tla, "DieHard.cfg": cfg },
});
console.log(output);  // what manyan prints, as TLC prints it
console.log(status);  // TLC's exit status: 12, an invariant is violated
```

`run(args, { files, stdin, signal })` runs manyan with the command line
`args` in a directory holding `files` (paths to text or bytes). It resolves
to the exit status, the output (standard output and error in order) and the
directory's files afterwards, so a counterexample written with
`-dumpTrace json trace.json` is `files["trace.json"]`. Aborting `signal`
stops the run.

It also resolves to `result`, what the check found as values, with no
text to parse:

```js
const { result } = await run(["DieHard"], { files });
result.violated;              // ["NotSolved"]
result.states.at(-1);         // { big: 4, small: 3 }
result.actions[1].name;       // "Next"
result.loop;                  // 0: the behavior ends; else the state it steps back to
result.distinct;              // 14
```

`states` holds the first counterexample the report prints whole, each a
record of the variables; `actions` the step into each, as
`TLCGet("action")` gives it, one more stepping back where there is a
loop. A TLA+ value is a boolean, number or string as itself, a tuple an
Array, a record (a function from names) an Object, another function a
Map, a set a Set, and any other, such as a model value, `{ "#tla": text }`,
TLC's text of it, which no record is: no name holds a `#`. See [index.d.ts](index.d.ts) and the manual's
[Library](https://github.com/soasme/manyan/blob/main/docs/manual.md#library).

Each run has a Worker of its own, so it does not block the page.
`npx manyan-wasm DieHard` runs it on the current directory's files.

## Differences from the executable

- One worker: WebAssembly cannot fork. `-workers` is accepted and the
  output is the same, as it is with any number of workers.
- `IOExec` and `IOEnvExec` cannot run a process.
- Memory is at most 4 GB.
- A browser gives a Worker about 1 MB of stack, where Node.js gives each
  run 64 MB: it holds a recursion about a thousand calls deep (1,600 of
  one through arithmetic, as `Sum(n) == n + Sum(n - 1)`), where TLC and
  the executable hold 5000. Past that, as a runaway recursion goes, the
  run rejects instead of printing TLC's StackOverflowError; `-stack 300`
  makes manyan print that error at a depth the browser holds.

For the full command line, see [the manual](https://github.com/soasme/manyan/blob/main/docs/manual.md);
for the native executable, `pip install manyan` or a
[release](https://github.com/soasme/manyan/releases).
