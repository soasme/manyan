#!/usr/bin/env node
// manyan on the command line, run by the WebAssembly build: the files of the
// current directory in, its standard input, what it wrote back out. The
// conformance suite runs it as an engine (make test-javascript).

import { readdirSync, readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { run } from "./index.js";

function walk(dir, files = {}) {
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const path = join(dir, entry.name);
    if (entry.isDirectory()) walk(path, files);
    else if (entry.isFile()) files[relative(".", path)] = readFileSync(path);
  }
  return files;
}

function input() {   // read to its end first
  if (process.stdin.isTTY) return "";
  try { return readFileSync(0, "utf8"); } catch { return ""; }   // a terminal's, non-blocking
}

const given = walk("."), stdin = input();
const { status, output, files } = await run(process.argv.slice(2), { files: given, stdin });
process.stdout.write(output);
for (const [path, data] of Object.entries(files))
  if (!given[path] || Buffer.compare(given[path], data)) {
    mkdirSync(dirname(path), { recursive: true });
    writeFileSync(path, data);
  }
process.exitCode = status;
