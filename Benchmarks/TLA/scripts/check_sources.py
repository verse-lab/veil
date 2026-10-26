#!/usr/bin/env python3
r"""Compare local TLA+ files with the pinned upstream files they cite.

Each checked file cites its source in a comment, as a GitHub URL pinned to a
full commit: https://github.com/OWNER/REPO/blob/COMMIT/PATH. Every cited file
of the same type (.tla or .cfg) is downloaded, and each pair gets one verdict:

  BYTE_IDENTICAL            The bytes are equal.
  COMMENTS_OR_SPACING_ONLY  The texts are equal after replacing every comment
                            character with a space and then deleting trailing
                            whitespace and blank lines. PlusCal algorithm text
                            counts as code although it sits in a comment.
                            Indentation and columns are kept, because TLA+
                            aligns /\ and \/ lists by column.
  CHANGED                   Anything else.

A verdict depends only on code_view(), code_lines() and verdict() below.
VERDICT_EXAMPLES specifies them on tricky inputs and runs before every
comparison; --self-test runs only the examples. Cited files of another type
(such as the TLA module that a CFG configures) are skipped.

The output directory holds report.json, the downloaded upstream files, and for
each pair pairs/NN-LOCAL-UPSTREAM/ with raw.diff, local.code and upstream.code
(the files with comments blanked; same lines and columns as the originals) and
code.diff (the compared lines; empty unless the verdict is CHANGED). Local
paths in the output are relative to the repository root.

Run from any directory (Python 3.9+, standard library only):
    python3 Benchmarks/TLA/scripts/check_sources.py --output /tmp/tla-source-review
    python3 Benchmarks/TLA/scripts/check_sources.py --file Benchmarks/TLA/TLAPlusExamples/Bakery.tla
    python3 Benchmarks/TLA/scripts/check_sources.py --self-test

By default all .tla and .cfg files under TLAPlusExamples/ are checked; --file
checks one file anywhere (path relative to the current directory). Exit 0
means the comparisons completed, NOT that the files are identical; exit 1
means a source could not be read or compared. No source files are modified.
This is a source audit, not a parser, a model-checking run, or a proof that
the upstream models, local adaptations, and Veil translations are
semantically equivalent.
"""

import argparse
import difflib
import hashlib
import json
import os
import re
import tempfile
import urllib.parse
import urllib.request
from collections import Counter
from pathlib import Path


REPO = Path(__file__).resolve().parents[3]
EXAMPLES_DIR = Path(__file__).resolve().parents[1] / "TLAPlusExamples"
SOURCE_URL = re.compile(
    r"https://github\.com/([\w.-]+/[\w.-]+)/blob/([^/\s]+)/"
    r"([^\s<>\"'`]+?\.(?:tla|cfg|launch))"
)
PLUSCAL = re.compile(r"--(?:fair\s+)?algorithm\b")


# The comparison. A verdict depends only on the three functions below.

def code_view(text):
    r"""Return text with every comment character replaced by a space.

    Comments run from "\*" to the end of the line, or from "(*" to the matching
    "*)" (block comments nest). Comment markers inside string literals are text.
    A block comment that contains a PlusCal algorithm keeps its text; only its
    delimiters and the comments inside it are blanked. Newlines are kept, so the
    view has the same lines and columns as the input.
    """
    out, i = [], 0
    while i < len(text):
        if text.startswith("\\*", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
        elif text.startswith("(*", i):
            end, depth = i + 2, 1
            while depth:
                if end >= len(text):
                    raise ValueError("Unterminated TLA+ comment")
                if text.startswith("(*", end):
                    depth, end = depth + 1, end + 2
                elif text.startswith("*)", end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
            body = text[i + 2:end - 2]
            out.append("  " + code_view(body) + "  " if PLUSCAL.search(body) else re.sub(r"[^\n]", " ", text[i:end]))
        elif text[i] == '"':
            end = i + 1
            while end < len(text) and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            if end >= len(text):
                raise ValueError("Unterminated TLA+ string")
            end += 1
            out.append(text[i:end])
        else:
            end = i + 1
            out.append(text[i])
        i = end
    return "".join(out)


def code_lines(text):
    """The lines a verdict compares: the code view without trailing whitespace and blank lines."""
    lines = (line.rstrip(" \t\r\f\v") for line in code_view(text).split("\n"))
    return [line for line in lines if line]


def verdict(local, upstream):
    """Classify a local file against its upstream file, both given as bytes."""
    if local == upstream:
        return "BYTE_IDENTICAL"
    if code_lines(local.decode("utf-8")) == code_lines(upstream.decode("utf-8")):
        return "COMMENTS_OR_SPACING_ONLY"
    return "CHANGED"


# The specification of verdict() by example: (verdict, what the local copy changes, upstream, local).
VERDICT_EXAMPLES = [
    ("BYTE_IDENTICAL", "nothing",
     "x == 1\n", "x == 1\n"),
    ("COMMENTS_OR_SPACING_ONLY", "adds a line comment",
     "x == 1\n", "\\* note\nx == 1\n"),
    ("COMMENTS_OR_SPACING_ONLY", "edits a block comment at the end of a line",
     "x == 1 (* a *)\n", "x == 1 (* longer *)\n"),
    ("COMMENTS_OR_SPACING_ONLY", "adds blank lines and trailing spaces",
     "x == 1\ny == 2\n", "x == 1   \n\n\ny == 2\n"),
    ("COMMENTS_OR_SPACING_ONLY", "edits code-like text inside a nested comment",
     "(* a (* b *) y == 1 *)\nx == 1\n", "(* a (* b *) y == 2 *)\nx == 1\n"),
    ("COMMENTS_OR_SPACING_ONLY", "edits a comment inside a PlusCal algorithm",
     "(*--algorithm A { x := 1 \\* a\n} *)\n", "(*--algorithm A { x := 1 \\* b\n} *)\n"),
    ("CHANGED", "changes a constant",
     "x == 1\n", "x == 2\n"),
    ("CHANGED", "comments out a definition",
     "x == 1\ny == 2\n", "x == 1\n\\* y == 2\n"),
    ("CHANGED", "moves a definition into a block comment",
     "x == 1\ny == 2\n", "x == 1\n(* y == 2 *)\n"),
    ("CHANGED", "edits code after a line comment that contains (*",
     "\\* (*\ny == 2\n", "\\* (*\ny == 3\n"),
    ("CHANGED", "edits code after a block comment that contains \\*",
     "(* a \\* b *) x == 1\n", "(* a \\* b *) x == 2\n"),
    ("CHANGED", "edits a string that contains comment markers",
     'x == "(* a *)"\n', 'x == "(* b *)"\n'),
    ("CHANGED", "re-indents a conjunction list",
     "x == /\\ a\n     /\\ b\n", "x == /\\ a\n       /\\ b\n"),
    ("CHANGED", "lengthens a comment that precedes code on its line",
     "x == (* a *) y\n", "x == (* abc *) y\n"),
    ("CHANGED", "edits a PlusCal statement",
     "(*--algorithm A { x := 1 } *)\n", "(*--algorithm A { x := 2 } *)\n"),
    ("CHANGED", "edits PlusCal in a comment that starts with a banner",
     "(*** PlusCal\n--algorithm A { x := 1 }\n***)\n", "(*** PlusCal\n--algorithm A { x := 2 }\n***)\n"),
    ("CHANGED", "moves a cfg value onto its keyword's line (conservative: TLC ignores layout)",
     "INVARIANT\n    Inv\n", "INVARIANT Inv\n"),
]


def self_test():
    """Run VERDICT_EXAMPLES and malformed inputs; return (description, specified, actual) rows."""
    rows = []
    for expected, what, upstream, local in VERDICT_EXAMPLES:
        try:
            rows.append((what, expected, verdict(local.encode(), upstream.encode())))
        except ValueError as error:
            rows.append((what, expected, f"ValueError: {error}"))
    for what, check, text in (("rejects an unterminated comment", code_view, "x == 1 (* a\n"),
                              ("rejects an unterminated string", code_view, 'x == "a\n'),
                              ("rejects a source URL not pinned to a commit", source_refs,
                               "https://github.com/o/r/blob/main/A.tla")):
        try:
            check(text)
            rows.append((what, "ValueError", "accepted"))
        except ValueError:
            rows.append((what, "ValueError", "ValueError"))
    return rows


# Plumbing: finding the cited sources, downloading them, and writing the evidence.

def source_refs(text):
    """Return (repository, commit, path) for each cited GitHub file; reject unpinned or unsafe URLs."""
    refs = list(dict.fromkeys(SOURCE_URL.findall(text)))
    if not refs:
        raise ValueError("No GitHub source file URL found")
    for repository, revision, source in refs:
        if not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise ValueError(f"Source URL is not pinned to a full commit: {revision}")
        if Path(source).is_absolute() or ".." in Path(repository + "/" + source).parts:
            raise ValueError(f"Invalid source path: {source}")
    return refs


def report_path(path):
    """Repository-relative path for reports, so they do not reveal local directories."""
    return os.path.relpath(path, REPO)


def git_blob(data):
    """Git's object id for these bytes; equals `git rev-parse COMMIT:PATH` in a clone of the upstream."""
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def check_files(paths, output):
    """Compare selected files, saving upstream copies and per-pair evidence; return the report."""
    rows = self_test()
    failed = [what for what, specified, actual in rows if actual != specified]
    self_test_result = f"{len(rows) - len(failed)}/{len(rows)} built-in examples behave as specified (see --self-test)"
    print("Self-test:", self_test_result)
    if failed:
        raise SystemExit("Self-test failed: " + "; ".join(failed))
    output.mkdir(parents=True, exist_ok=True)
    jobs, results, errors, skipped = [], [], [], []
    for path in paths:
        try:
            refs = source_refs(path.read_text(encoding="utf-8"))
        except (OSError, ValueError) as error:
            errors.append({"local": report_path(path), "error": str(error)})
            continue
        matching = [(path, repository, revision, source) for repository, revision, source in refs
                    if Path(source).suffix == path.suffix]
        if not matching:
            skipped.append({"local": report_path(path), "reason": "Upstream reference has a different file type"})
        jobs.extend(matching)

    downloaded = {}
    for index, (path, repository, revision, source) in enumerate(jobs, 1):
        url = f"https://github.com/{repository}/blob/{revision}/{source}"
        raw_url = f"https://raw.githubusercontent.com/{repository}/{revision}/{source}"
        try:
            local = path.read_bytes()
            if raw_url not in downloaded:
                with urllib.request.urlopen(raw_url, timeout=30) as response:
                    downloaded[raw_url] = response.read()
                cached = output / "upstream" / repository / revision / source
                cached.parent.mkdir(parents=True, exist_ok=True)
                cached.write_bytes(downloaded[raw_url])
            upstream = downloaded[raw_url]
            local_text, upstream_text = local.decode("utf-8"), upstream.decode("utf-8")
            local_lines, upstream_lines = code_lines(local_text), code_lines(upstream_text)
            evidence = output / "pairs" / f"{index:02d}-{path.name}-{Path(source).name}"
            evidence.mkdir(parents=True, exist_ok=True)
            (evidence / "local.code").write_bytes(code_view(local_text).encode("utf-8"))
            (evidence / "upstream.code").write_bytes(code_view(upstream_text).encode("utf-8"))
            for name, old, new in (("raw.diff", upstream_text.splitlines(), local_text.splitlines()),
                                   ("code.diff", upstream_lines, local_lines)):
                diff = difflib.unified_diff(old, new, fromfile=url, tofile=report_path(path), lineterm="")
                (evidence / name).write_text("".join(line + "\n" for line in diff), encoding="utf-8")
            result = {"local": report_path(path), "source_url": url, "download_url": raw_url,
                      "repository": repository, "commit": revision, "path": urllib.parse.unquote(source),
                      "status": verdict(local, upstream),
                      "compared_lines": {"local": len(local_lines), "upstream": len(upstream_lines)},
                      "local_sha256": hashlib.sha256(local).hexdigest(),
                      "upstream_sha256": hashlib.sha256(upstream).hexdigest(),
                      "upstream_git_blob": git_blob(upstream),
                      "evidence": f"pairs/{evidence.name}"}
            results.append(result)
            print(f"{result['status']:24} {path.name} <- {repository}@{revision[:7]}:{Path(source).name}")
        except (OSError, ValueError) as error:
            errors.append({"local": report_path(path), "source_url": url, "error": str(error)})

    return {"scope": "Pinned GitHub source identity; no semantic equivalence claim",
            "self_test": self_test_result, "results": results, "errors": errors, "skipped": skipped}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path, help="Evidence directory (default: a new temporary directory)")
    parser.add_argument("--file", type=Path, help="Check only this local file (path relative to the current directory)")
    parser.add_argument("--self-test", action="store_true", help="Only run the built-in examples (no network access)")
    args = parser.parse_args()
    if args.self_test:
        rows = self_test()
        for what, specified, actual in rows:
            print(f"{'ok' if actual == specified else 'FAIL':4} {specified:24} {what}"
                  + ("" if actual == specified else f" (got {actual})"))
        return 0 if all(actual == specified for _, specified, actual in rows) else 1
    output = args.output or Path(tempfile.mkdtemp(prefix="tla-source-review-"))
    paths = [args.file.resolve()] if args.file is not None else sorted(
        path for path in EXAMPLES_DIR.rglob("*") if path.is_file() and path.suffix in (".tla", ".cfg"))
    report = check_files(paths, output)
    (output / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("\nComparison counts:", dict(Counter(item["status"] for item in report["results"])))
    for item in report["skipped"]:
        print("SKIPPED:", item)
    for error in report["errors"]:
        print("ERROR:", error)
    print("Evidence:", output.resolve())
    print("Differences require review; completed comparisons do not prove semantic equivalence.")
    return 1 if report["errors"] or not report["results"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
