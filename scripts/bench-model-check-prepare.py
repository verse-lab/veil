#!/usr/bin/env python3
"""Write the evaluation versions of Veil benchmark specifications.

In each given .lean file, the checks that are only for testing are between two `-- TEST ONLY`
lines, and those of the evaluation are commented out in `/- EVAL ... -/` blocks:

  -- TEST ONLY
  #model_check { n := 3 }
  -- TEST ONLY

  /- EVAL
  #model_check compiled { n := 10 } {} (seenSet := HAMTMapShard)
  -/

The evaluation version deletes the TEST ONLY regions, marker lines included, and the
`#gen_executable` commands, so that `#model_check` generates the executable definitions itself
(with the same default options) and the time it takes is reported; it uncomments the EVAL blocks
and keeps the rest of the file as it is. Every marker and `#gen_executable` is on a line of its
own, and an EVAL block contains no comment delimiters. A file must have an EVAL block with a
`#model_check`, and the only `#model_check` commands of its evaluation version must be those of
its EVAL blocks.

The versions are written to OUT_DIR, as NAME.lean for an argument NAME=FILE and under the name of
the file otherwise, after the .lean files there are deleted. If a file breaks the rules above,
nothing is written.

usage: python3 scripts/bench-model-check-prepare.py OUT_DIR [NAME=]FILE...
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

TEST_ONLY = "-- TEST ONLY"
EVAL_OPEN = "/- EVAL"
EVAL_CLOSE = "-/"
MODEL_CHECK = "#model_check"
GEN_EXECUTABLE = "#gen_executable"


class MarkerError(Exception):
    pass


def commands_in_code(text: str, command: str) -> int:
    """The number of `command` commands in `text`, outside comments and string literals."""
    count, i, depth = 0, 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("'\"'", i):    # the only character literal that would start a string
            i += 3
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        elif text.startswith(command, i):
            i += len(command)
            following = text[i:i + 1]
            if not (following.isalnum() or following in ("_", "'", "!", "?")):
                count += 1
        else:
            i += 1
    return count


def prepare(text: str) -> tuple[str, int, int, int, int]:
    """The evaluation version of `text`, with its numbers of TEST ONLY regions and of
    `#gen_executable` commands deleted, of EVAL blocks uncommented and of `#model_check` commands
    in them."""
    out, evals = [], []
    region, start, regions, gen_executables = None, 0, 0, 0
    for number, line in enumerate(text.splitlines(keepends=True), 1):
        marker = line.strip()
        if ("TEST ONLY" in marker and marker != TEST_ONLY
                or re.match(r"/-\s*EVAL\b", marker) and marker != EVAL_OPEN):
            raise MarkerError(f"line {number}: a marker must be alone on its line, "
                              f"as `{TEST_ONLY}` or `{EVAL_OPEN}`")
        if region == "test":
            if marker == TEST_ONLY:
                region = None
            elif marker == EVAL_OPEN:
                raise MarkerError(f"line {number}: an EVAL block in the TEST ONLY region of line {start}")
        elif region == "eval" and marker == EVAL_CLOSE:
            region = None
        elif region == "eval" and (marker == TEST_ONLY or "/-" in line or "-/" in line):
            raise MarkerError(f"line {number}: a marker or a comment delimiter in the EVAL block of line {start}")
        elif marker == GEN_EXECUTABLE:
            gen_executables += 1
        elif region == "eval":
            out.append(line)
            evals[-1] += line
        elif marker == TEST_ONLY:
            region, start, regions = "test", number, regions + 1
        elif marker == EVAL_OPEN:
            region, start = "eval", number
            evals.append("")
        else:
            out.append(line)
    if region:
        raise MarkerError(f"line {start}: the {'TEST ONLY region' if region == 'test' else 'EVAL block'} "
                          "is not closed")
    checks = commands_in_code("".join(evals), MODEL_CHECK)
    if not checks:
        raise MarkerError("no EVAL block with a #model_check")
    result = "".join(out)
    others = commands_in_code(result, MODEL_CHECK) - checks
    if others:
        raise MarkerError(f"{others} #model_check command(s) outside the TEST ONLY regions and the EVAL blocks")
    if commands_in_code(result, GEN_EXECUTABLE):
        raise MarkerError(f"a {GEN_EXECUTABLE} that is not alone on its line, e.g. with options")
    return result, regions, gen_executables, len(evals), checks


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out_dir", help="where to write the evaluation versions")
    ap.add_argument("files", nargs="+", metavar="[NAME=]FILE", help="the .lean files of the benchmarks")
    args = ap.parse_args()
    out_dir = pathlib.Path(args.out_dir)
    versions, failed = {}, False
    for arg in args.files:
        name, separator, file = arg.partition("=")
        if not separator:
            name, file = "", arg
        path = pathlib.Path(file)
        name = name or path.stem
        if not re.fullmatch(r"[A-Za-z0-9_]+", name):
            sys.exit(f"{arg}: a name consists of letters, digits and underscores")
        # Also on a case-insensitive file system
        if name.lower() in (other.lower() for other in versions):
            sys.exit(f"{arg}: the name {name} is taken")
        try:
            text, regions, gen_executables, blocks, checks = prepare(path.read_text(encoding="utf-8"))
        except (OSError, MarkerError) as e:
            print(f"{path}: {e}", file=sys.stderr)
            failed = True
            continue
        versions[name] = text
        print(f"{path} -> {name}.lean: deleted {regions} TEST ONLY region(s) and {gen_executables} "
              f"{GEN_EXECUTABLE}, uncommented {blocks} EVAL block(s) with {checks} #model_check")
    if failed:
        sys.exit("no evaluation version written")
    out_dir.mkdir(parents=True, exist_ok=True)
    for stale in out_dir.glob("*.lean"):
        stale.unlink()
    for name, text in versions.items():
        (out_dir / f"{name}.lean").write_text(text, encoding="utf-8")
    print(f"wrote {len(versions)} evaluation version(s) to {out_dir}")


if __name__ == "__main__":
    main()
