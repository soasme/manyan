/** A TLA+ value: a boolean, number or string as itself, a tuple as an Array, a
 * record (a function from names) as an Object, another function as a Map, a
 * set as a Set; any other, as a model value, as `{ "#tla": text }`, TLC's text
 * of it, which no record is: no name holds a #. */
export type Value =
  | boolean | number | string | Value[] | { [field: string]: Value } | Map<Value, Value> | Set<Value>
  | { "#tla": string };

/** What the check found, as manyan.h's ManyanResult gives it. */
export interface ManyanResult {
  /** The first counterexample printed whole: each state a record of the variables that have a value. */
  states: Record<string, Value>[];
  /** The step into each state, as TLCGet("action") gives it; with a loop, one more steps back. */
  actions: { name: string; location: Record<string, Value>; [field: string]: Value }[];
  /** The state, from 1, the last steps back to: its own where it stutters; 0 for none. */
  loop: number;
  /** The invariants and properties the report names violated. */
  violated: string[];
  /** The counts reported last; null where none is. */
  generated: number | null;
  distinct: number | null;
  left: number | null;
  depth: number | null;
}

export interface Result {
  /** The exit status, TLC's: 0, or 12 for a violated invariant, ... */
  status: number;
  /** What manyan printed, standard output and error in order. */
  output: string;
  /** The directory's files after the run, those manyan wrote among them. */
  files: Record<string, Uint8Array>;
  /** What the check found, as values. */
  result: ManyanResult;
}

/** Run manyan with the command line `args` in a directory holding `files`. */
export function run(
  args: string[],
  options?: { files?: Record<string, string | Uint8Array>; stdin?: string; signal?: AbortSignal },
): Promise<Result>;
