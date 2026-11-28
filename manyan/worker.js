// The Worker of a run (index.js): runs manyan once and posts what it gave.

import { check } from "./engine.js";

const node = typeof process === "object" && process.versions?.node;
const port = node ? (await import("node:worker_threads")).parentPort : self;
const listen = node ? (fn) => port.once("message", fn) : (fn) => port.addEventListener("message", (e) => fn(e.data), { once: true });

listen(async ({ module, args, files, stdin }) => {
  try {
    const result = await check(module, args, files, stdin);
    port.postMessage(result, Object.values(result.files).map((f) => f.buffer));
  } catch (e) {
    port.postMessage({ error: e?.message ?? String(e) });
  }
});
