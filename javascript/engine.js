// One run of manyan in this thread: a fresh instance of the module, as each
// run of the executable is a new process, on files in memory.

import createManyan from "./manyan.mjs";

export async function check(module, args, files, stdin) {
  const input = new TextEncoder().encode(stdin);
  let at = 0;
  const output = [];
  const m = await createManyan({
    noInitialRun: true,
    instantiateWasm: (imports, done) => { WebAssembly.instantiate(module, imports).then((i) => done(i, module)); return {}; },
    preRun: [(m) => m.FS.init(() => (at < input.length ? input[at++] : null), (c) => output.push(c), (c) => output.push(c))],
  });
  m.FS.mkdir("/work");
  for (const [path, data] of Object.entries(files)) {
    const parts = path.split("/");
    for (let i = 1; i < parts.length; i++) {
      const dir = "/work/" + parts.slice(0, i).join("/");
      if (!m.FS.analyzePath(dir).exists) m.FS.mkdir(dir);
    }
    m.FS.writeFile("/work/" + path, data);
  }
  m.FS.chdir("/work");
  let status;
  try {
    status = m.callMain(args);
  } catch (e) {
    if (e instanceof RangeError) throw new Error("manyan: the thread's stack ran out, before TLC's would: " +
      "-stack 300 gives TLC's StackOverflowError where a browser's stack holds no more");
    if (e?.name !== "ExitStatus") throw e;
    status = e.status;
  }
  return { status, output: new TextDecoder().decode(new Uint8Array(output.map((c) => c & 255))), files: read(m.FS, "/work", "") };
}

function read(FS, dir, prefix) {
  const files = {};
  for (const name of FS.readdir(dir)) {
    if (name === "." || name === "..") continue;
    const path = dir + "/" + name;
    if (FS.isDir(FS.stat(path).mode)) Object.assign(files, read(FS, path, prefix + name + "/"));
    else files[prefix + name] = FS.readFile(path);
  }
  return files;
}
