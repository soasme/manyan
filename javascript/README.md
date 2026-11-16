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

Each run has a Worker of its own, so it does not block the page.
`npx manyan-wasm DieHard` runs it on the current directory's files.

## Differences from the executable

- One worker: WebAssembly cannot fork. `-workers` is accepted and the
  output is the same, as it is with any number of workers.
- `IOExec` and `IOEnvExec` cannot run a process.
- Memory is at most 4 GB.
- A browser gives a Worker about 1 MB of stack, where Node.js gives each
  run 64 MB: past a few hundred nested calls, as a runaway recursion
  makes, the run rejects instead of printing TLC's StackOverflowError.
  `-stack 300` makes manyan print that error at a depth the browser holds.

For the full command line, see [the manual](https://github.com/soasme/manyan/blob/main/docs/manual.md);
for the native executable, `pip install manyan` or a
[release](https://github.com/soasme/manyan/releases).
