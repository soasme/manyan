"""CLI entry point for `python -m manyan`.

Runs the native `manyan` executable for TLA+ specifications, and analyses +
model-checks Python source files annotated with `temporal`:

    python -m manyan check path/to/file.py [...]
    python -m manyan emit path/to/file.py [...]
    python -m manyan path/to/file.py
    python -m manyan [manyan-tla-flags] examples/DieHard
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from typing import Optional

from manyan import (
    Run,
    TemporalCompileError,
    check_temporal,
    emit_temporal,
    find_manyan_bin,
)


def _format_trace(run_res: Run) -> str:
    r = run_res.result
    if r is None or not r.states:
        return ""
    lines: list[str] = []
    for idx, state in enumerate(r.states, start=1):
        act = r.actions[idx - 1]["name"] if idx - 1 < len(r.actions) else ""
        label = f" <{act}>" if act else ""
        lines.append(f"  State {idx}:{label}")
        for k, v in state.items():
            lines.append(f"    {k} = {v!r}")
    if r.loop:
        lines.append(f"  Back to state {r.loop}")
    return "\n".join(lines)


def _run_temporal_cli(subcmd: str, argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog=f"manyan {subcmd}")
    parser.add_argument("paths", nargs="+", help="Python source files or directories")
    parser.add_argument("--spec", default=None, help="Check only the named specification class or function")
    parser.add_argument("--model", default=None, help="Check only the named Model declaration")
    parser.add_argument("--spec-only", action="store_true", help="Check declared specifications without implementation bodies")
    if subcmd == "check":
        parser.add_argument("--workers", "-workers", type=int, default=1, help="Number of worker processes")
        parser.add_argument("--no-deadlock", "-deadlock", action="store_true", help="Disable deadlock checking")
        parser.add_argument("--symbolic", "-symbolic", action="store_true", help="Use symbolic checking (-symbolic)")
        parser.add_argument("--length", "-length", type=int, default=None, help="Bound length for -symbolic")
        parser.add_argument("--emit", action="store_true", help="Also print generated TLA+ and .cfg")
        parser.add_argument("--verbose", "-v", action="store_true", help="Print full Manyan output")

    args = parser.parse_args(argv)
    mode = "spec-only" if args.spec_only else "all"

    if subcmd == "emit":
        any_found = False
        for p in args.paths:
            try:
                models = emit_temporal(p, spec=args.spec, model=args.model, mode=mode)
            except (FileNotFoundError, TemporalCompileError, SyntaxError) as exc:
                print(f"error: {p}: {exc}", file=sys.stderr)
                return 1
            for cm in models:
                any_found = True
                print(f"% === {cm.source or p} :: {cm.name} ({cm.module_name}.tla) ===")
                print(cm.tla, end="")
                print(f"% === {cm.module_name}.cfg ===")
                print(cm.cfg, end="")
        if not any_found:
            print("error: no Temporal specifications found", file=sys.stderr)
            return 1
        return 0

    exit_code = 0
    total = 0
    passed = 0
    for p in args.paths:
        try:
            runs = check_temporal(
                p,
                spec=args.spec,
                model=args.model,
                mode=mode,
                workers=args.workers,
                check_deadlock=False if args.no_deadlock else None,
                symbolic=args.symbolic,
                length=args.length,
            )
        except (FileNotFoundError, TemporalCompileError, SyntaxError) as exc:
            print(f"error: {p}: {exc}", file=sys.stderr)
            return 1

        for tr in runs:
            total += 1
            loc = tr.compiled.source or p
            label = f"{loc}::{tr.name}"
            if args.emit:
                print(tr.compiled.tla, end="")
                print(tr.compiled.cfg, end="")
            if tr.ok:
                passed += 1
                distinct = tr.run.result.distinct if tr.run.result else None
                extra = f" ({distinct} distinct states)" if distinct is not None else ""
                print(f"PASS {label}{extra}")
                if args.verbose:
                    print(tr.run.output, end="")
            else:
                if exit_code == 0:
                    exit_code = tr.run.status or 1
                violated = (
                    ", ".join(tr.run.result.violated)
                    if tr.run.result and tr.run.result.violated
                    else f"exit {tr.run.status}"
                )
                print(f"FAIL {label}: {violated}")
                if args.verbose:
                    print(tr.run.output, end="")
                else:
                    trace = _format_trace(tr.run)
                    if trace:
                        print(trace)
                    else:
                        print(tr.run.output.strip())

    if total == 0:
        print("error: no Temporal specifications found", file=sys.stderr)
        return 1
    if exit_code == 0:
        print(f"Checked {total} Temporal model(s): {passed} passed.")
    else:
        print(f"Checked {total} Temporal model(s): {passed} passed, {total - passed} failed.")
    return exit_code


def _is_python_target(argv: list[str]) -> bool:
    return any(not arg.startswith("-") and arg.endswith(".py") for arg in argv)


def main(argv: Optional[list[str]] = None) -> None:
    args = list(sys.argv[1:] if argv is None else argv)
    if args and args[0] in ("check", "emit"):
        sys.exit(_run_temporal_cli(args[0], args[1:]))
    if _is_python_target(args):
        sys.exit(_run_temporal_cli("check", args))

    manyan = find_manyan_bin()
    if sys.platform == "win32":
        sys.exit(subprocess.call([manyan, *args]))
    os.execv(manyan, [manyan, *args])


if __name__ == "__main__":
    main()
