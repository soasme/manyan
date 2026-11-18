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
  return { status, output: new TextDecoder().decode(new Uint8Array(output.map((c) => c & 255))), files: read(m.FS, "/work", ""),
           result: result(m) };
}

// What the run found (manyan.h's ManyanResult), its values made JavaScript's.
function result(m) {
  const r = m._manyan_main_result(), word = (at) => m.getValue(r + at, "*");
  const count = (at) => { const n = Number(m.getValue(r + at, "i64")); return n < 0 ? null : n; };
  const length = word(0), loop = word(12), list = (at, n) => Array.from({ length: n }, (_, i) => value(m, m.getValue(at + 4 * i, "*")));
  const violated = [];
  for (let p = word(16); p && m.getValue(p, "*"); p += 4) violated.push(m.UTF8ToString(m.getValue(p, "*")));
  return {
    states: list(word(4), length), actions: list(word(8), length + (loop > 0)), loop, violated,
    generated: count(24), distinct: count(32), left: count(40), depth: count(48),
  };
}

// A TLA+ value: a boolean, number or string as itself, a tuple as an Array, a
// record (a function from names) as an Object, another function as a Map, a
// set as a Set; any other, as a model value, as { "#tla": TLC's text of it },
// which no record is: no name holds a #.
const NAME = /^\w*[A-Za-z]\w*$/;
function value(m, v) {
  const n = () => m._manyan_size(v), each = (f) => Array.from({ length: n() }, (_, i) => f(i));
  switch (m._manyan_kind(v)) {
    case 0: return m._manyan_is_true(v) !== 0;
    case 1: return Number(m._manyan_int_value(v));
    case 2: return m.UTF8ToString(m._manyan_string_value(v, 0));
    case 4: return each((i) => value(m, m._manyan_value(v, i)));
    case 5: {
      const pairs = each((i) => [value(m, m._manyan_key(v, i)), value(m, m._manyan_value(v, i))]);
      return pairs.every(([k]) => NAME.test(k)) ? Object.fromEntries(pairs) : new Map(pairs);
    }
    case 6: {
      const e = m._manyan_elements(v);
      if (e) return new Set(Array.from({ length: m._manyan_size(e) }, (_, i) => value(m, m._manyan_element(e, i))));
    }
  }
  return { "#tla": m.UTF8ToString(m._manyan_print(v)) };
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
