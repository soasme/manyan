// The result run() gives beside the output: what the check found, as values.
// `make test-javascript` runs it.
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { run } from "./index.js";

const example = (name) => readFileSync(new URL(`../examples/${name}`, import.meta.url), "utf8");
const spec = (name, body, cfg) => ({ [`${name}.tla`]: `---- MODULE ${name} ----\n${body}\n====\n`, [`${name}.cfg`]: cfg });
const test = async (name, args, files, check) => {
  const r = await run(args, { files });
  try { check(r.result, r); } catch (e) { e.message = `${name}: ${e.message}\n${r.output}`; throw e; }
  console.log(`PASS ${name}`);
};

await test("an invariant", ["DieHard"], { "DieHard.tla": example("DieHard.tla"), "DieHard.cfg": example("DieHard.cfg") }, (r, { status }) => {
  assert.equal(status, 12);
  assert.deepEqual(r.violated, ["NotSolved"]);
  assert.equal(r.states.length, 7);
  assert.deepEqual(r.states[0], { big: 0, small: 0 });
  assert.deepEqual(r.states.at(-1), { big: 4, small: 3 });
  assert.equal(r.actions.length, 7);
  assert.equal(r.actions[0].name, "Init");
  assert.equal(r.actions[1].name, "Next");
  assert.deepEqual(r.actions[1].location, { beginLine: 9, beginColumn: 12, endLine: 9, endColumn: 37, module: "DieHard" });
  assert.equal(r.loop, 0);
  assert.deepEqual([r.generated, r.distinct, r.left, r.depth], [73, 14, 1, 7]);
});

await test("values", ["V"], spec("V", `EXTENDS Naturals
CONSTANT M
VARIABLE t, r, f, s, m, g
Init == t = <<1, "a", TRUE>> /\\ r = [a |-> {1, 2}, tla |-> "M"] /\\ f = [i \\in {0, 1} |-> i = 0] /\\ s = {} /\\ m = M
  /\\ g = [k \\in {"a b", "#tla"} |-> 0]
Next == UNCHANGED <<t, r, f, s, m, g>>
Inv == s # {}`, "CONSTANT M = M\nINIT Init\nNEXT Next\nINVARIANT Inv\n"), (r) => {
  assert.deepEqual(r.violated, ["Inv"]);
  assert.deepEqual(r.states, [{
    t: [1, "a", true], r: { a: new Set([1, 2]), tla: "M" }, f: new Map([[0, true], [1, false]]), s: new Set(),
    m: { "#tla": "M" }, g: new Map([["#tla", 0], ["a b", 0]]),
  }]);
  assert.deepEqual(r.actions.map((a) => a.name), ["Init"]);
});

const cycle = (property, fair) => spec("L", `EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\\ [][Next]_x${fair ? " /\\ WF_x(Next)" : ""}
P == ${property}`, "SPECIFICATION Spec\nPROPERTY P\n");

await test("a lasso", ["L"], cycle("<>(x = 5)", true), (r, { status }) => {
  assert.equal(status, 13);
  assert.deepEqual(r.violated, ["P"]);
  assert.deepEqual(r.states, [{ x: 0 }, { x: 1 }, { x: 2 }]);
  assert.equal(r.loop, 1);
  assert.deepEqual(r.actions.map((a) => a.name), ["Init", "Next", "Next", "Next"]);
});

await test("stuttering", ["L"], cycle("<>(x = 1)", false), (r) => {
  assert.deepEqual(r.states, [{ x: 0 }]);
  assert.equal(r.loop, 1);
  assert.equal(r.actions.length, 2);
});

await test("no error", ["L"], cycle("[](x < 3)", true), (r, { status }) => {
  assert.equal(status, 0);
  assert.deepEqual([r.states, r.actions, r.loop, r.violated], [[], [], 0, []]);
  assert.deepEqual([r.generated, r.distinct, r.left, r.depth], [4, 3, 0, 3]);
});

const simulated = spec("S", "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nInv == x < 2",
  "INIT Init\nNEXT Next\nINVARIANT Inv\n");
await test("a simulation", ["-simulate", "-seed", "1", "S"], simulated, (r, { status }) => {
  assert.equal(status, 12);
  assert.deepEqual(r.states, [{ x: 0 }, { x: 1 }, { x: 2 }]);
  assert.equal(r.generated, 3);
  assert.deepEqual([r.distinct, r.left, r.depth], [null, null, null]);
});

await test("a simulation with no error", ["-simulate", "num=2", "-depth", "3", "L"], cycle("[](x < 3)", true), (r) => {
  assert.deepEqual([r.states, r.generated], [[], null]);   /* it reports no counts */
});

await test("a parse error", ["P"], spec("P", "VARIABLE", "INIT Init\n"), (r, { status }) => {
  assert.equal(status, 150);
  assert.deepEqual([r.states, r.violated, r.generated], [[], [], null]);
});

await test("-version", ["-version"], {}, (r, { output }) => {
  assert.equal(r, null);
  assert.match(output, /^manyan version /);
});

await test("a usage error", ["-workers"], {}, (r) => {
  assert.equal(r, null);
});
