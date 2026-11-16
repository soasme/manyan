// Manyan compiled to WebAssembly: the same program as the manyan executable,
// run on files given in memory. Each run has a Worker of its own, as each run
// of the executable is a process, so it neither blocks the caller nor
// outlives a signal. WebAssembly cannot fork: it checks with one worker,
// which prints what any number print.

const node = typeof process === "object" && process.versions?.node;
const NodeWorker = node ? (await import("node:worker_threads")).Worker : null;
const WORKER = new URL("./worker.js", import.meta.url);
const STACK_MB = 64; // evaluation nests 5000 deep before TLC's StackOverflowError, as natively

let compiled;
function compile() {
  compiled ??= (async () => {
    const url = new URL("./manyan.wasm", import.meta.url);
    const bytes = node ? await (await import("node:fs/promises")).readFile(url) : await (await fetch(url)).arrayBuffer();
    return WebAssembly.compile(bytes);
  })();
  return compiled;
}

/**
 * Run manyan with the command line `args` in a directory holding `files`,
 * an object of paths to text or bytes, with the text `stdin` as its standard
 * input. Resolves to the exit status, what it printed to standard output and
 * error in order, and the directory's files afterwards, those it wrote among
 * them. Aborting `signal` stops it and rejects.
 */
export async function run(args, { files = {}, stdin = "", signal } = {}) {
  const module = await compile();
  signal?.throwIfAborted();
  const worker = node ? new NodeWorker(WORKER, { resourceLimits: { stackSizeMb: STACK_MB } }) : new Worker(WORKER, { type: "module" });
  const on = (event, fn) => (node ? worker.on(event, fn) : worker.addEventListener(event, (e) => fn(e.data ?? e)));
  try {
    return await new Promise((resolve, reject) => {
      signal?.addEventListener("abort", () => reject(signal.reason), { once: true });
      on("message", (r) => (r.error ? reject(new Error(r.error)) : resolve(r)));
      on("error", (e) => reject(e instanceof Error ? e : new Error(e.message ?? String(e))));
      if (node) worker.on("exit", (code) => reject(new Error(`manyan: its worker exited with ${code}`)));
      worker.postMessage({ module, args, files, stdin });
    });
  } finally {
    worker.terminate();
  }
}
