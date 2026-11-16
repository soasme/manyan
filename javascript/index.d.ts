export interface Result {
  /** The exit status, TLC's: 0, or 12 for a violated invariant, ... */
  status: number;
  /** What manyan printed, standard output and error in order. */
  output: string;
  /** The directory's files after the run, those manyan wrote among them. */
  files: Record<string, Uint8Array>;
}

/** Run manyan with the command line `args` in a directory holding `files`. */
export function run(
  args: string[],
  options?: { files?: Record<string, string | Uint8Array>; stdin?: string; signal?: AbortSignal },
): Promise<Result>;
