#!/usr/bin/env python3
"""Compare the pinned Cosmos DB source and the current finite TLC/Veil cases."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from urllib.request import urlopen


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REVISION = "a8357c9c0a8d0ed710c68a64bc3a9ed0dc860a8a"
UPSTREAM = f"https://raw.githubusercontent.com/Azure/azure-cosmos-tla/{REVISION}"
INVARIANTS = ("Eventual", "Session", "Bounded_Staleness", "Strong")
MODES = (*INVARIANTS, "Consistent_Prefix")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(command, cwd, log, timeout=300):
    log.with_suffix(".command.json").write_text(json.dumps(command, indent=2) + "\n")
    with log.open("w") as output:
        result = subprocess.run(command, cwd=cwd, stdout=output,
                                stderr=subprocess.STDOUT, timeout=timeout)
    return result.returncode, log.read_text()


def read_case(path):
    # Accept only the configuration form supported by this comparison. In
    # particular, do not silently ignore added constraints, views or properties.
    text = re.sub(r"\\\*[^\n]*", "", path.read_text())
    match = re.fullmatch(
        r'\s*SPECIFICATION Spec\s+CONSTANTS\s+NumClients = (\d+)\s+'
        r'MaxNumOp = (\d+)\s+Consistency = "(\w+)"\s+K = (\d+)\s+'
        r'CHECK_DEADLOCK FALSE\s+INVARIANTS?\s+([\w\s]+)', text)
    require(match, f"Unsupported CFG syntax: {path.name}")
    clients, maximum, mode, k, invariants = match.groups()
    require(int(clients) == 1 and int(maximum) < 10 and mode in MODES,
            f"CFG outside the reviewed source domain: {path.name}")
    selected = invariants.split()
    require(selected and all(name in MODES for name in selected),
            f"Unknown invariant in {path.name}")
    mapped = {"Eventual" if name == "Consistent_Prefix" else name
              for name in selected}
    return {"cfg": path.name, "maximum": int(maximum), "mode": mode,
            "k": int(k), "invariants": [n for n in INVARIANTS if n in mapped]}


def check_upstream(output):
    for remote, local in (("scenario1/swscop.tla", "swscop.tla"),
                          ("LICENSE", "LICENSE")):
        with urlopen(f"{UPSTREAM}/{remote}", timeout=30) as response:
            upstream = response.read()
        (output / f"upstream-{local}").write_bytes(upstream)
        current = (HERE / local).read_bytes()
        if local == "LICENSE":
            require(current == upstream, "LICENSE differs from the pinned upstream license")
        else:
            # Only initial line comments and trailing whitespace may differ.
            def model(text):
                header, body = text.decode().split("\nEXTENDS", 1)
                lines = header.splitlines()
                require(all(not line.strip() or line.lstrip().startswith(r"\*")
                            for line in lines[1:]), "Unexpected source header content")
                return lines[0], body.rstrip()
            require(model(current) == model(upstream),
                    "TLA+ differs from upstream beyond initial comments/trailing whitespace")


def check_veil(cases, output):
    source = (ROOT / "Examples/TLA/CosmosDB.lean").read_text()
    header, body = source.split("veil module SWSCOP", 1)
    body = body.split("-- ==================== Model checking ====================", 1)[0]
    declarations, generation = body.split("#gen_spec", 1)
    matches = list(re.finditer(r"^invariant \[(\w+)\]", declarations, re.MULTILINE))
    require(tuple(match[1] for match in matches) == INVARIANTS,
            "Translation invariant layout changed; review the harness")
    blocks = {match[1]: declarations[match.start():
              matches[i + 1].start() if i + 1 < len(matches) else len(declarations)]
              for i, match in enumerate(matches)}
    # Reuse the current actions and initial state verbatim. Only invariant
    # selection and the surrounding module name differ between these copies.
    driver = header
    lines = {}
    selections = sorted({tuple(case["invariants"]) for case in cases})
    for index, selection in enumerate(selections):
        namespace = f"CosmosCheck{index}"
        driver += f"veil module {namespace}" + declarations[:matches[0].start()]
        driver += "".join(blocks[name] for name in selection)
        driver += "#gen_spec" + generation
        for case in cases:
            if tuple(case["invariants"]) != selection:
                continue
            driver += f'\n-- {case["cfg"]}\n'
            lines[len(driver.splitlines()) + 1] = case["cfg"]
            driver += (
                "#model_check interpreted\n"
                "  { client := Fin 1 }\n"
                f'  {{ oneClient := 0, MaxNumOp := {case["maximum"]}, K := {case["k"]},\n'
                f'    Consistency := ConsistencyLevel.{case["mode"]} }}\n'
                "  (sequential := true) (fingerprintType := UInt64)\n")
        driver += f"end {namespace}\n\n"
    path = output / "Checks.lean"
    path.write_text(driver)
    code, log = run(["lake", "env", "lean", "--json", str(path)], ROOT,
                    output / "veil.jsonl")
    results = {}
    for line in log.splitlines():
        message = json.loads(line)
        data = message.get("data", "")
        case = lines.get(message.get("pos", {}).get("line"))
        passed = re.search(r"No violation \(explored (\d+) states\)", data)
        failed = re.search(r"Violation: safety_failure \(violates: (\w+)\)", data)
        if case and (passed or failed):
            require(case not in results, f"Duplicate Veil result for {case}")
            if passed:
                results[case] = {"distinct": int(passed[1])}
            else:
                trace = re.findall(r"^\s*State (\d+) \(via", data, re.MULTILINE)
                require(trace, f"Missing Veil trace for {case}")
                results[case] = {"violation": failed[1],
                                 "transitions": max(map(int, trace))}
        else:
            require(message.get("severity") != "error", f"Unexpected Lean error: {data}")
    require(set(results) == {case["cfg"] for case in cases}, "Missing Veil results")
    require(code == (1 if any("violation" in r for r in results.values()) else 0),
            f"Unexpected Lean exit status: {code}")
    return results


def check_tlc(case, jar, output):
    directory = output / Path(case["cfg"]).stem
    directory.mkdir()
    code, log = run(
        ["java", "-XX:+UseParallelGC", "-Xmx512m", "-cp", str(jar), "tlc2.TLC",
         "-workers", "1", "-noGenerateSpecTE", "-metadir", str(directory / "states"),
         "-config", str(HERE / case["cfg"]), str(HERE / "swscop.tla")],
        directory, directory / "tlc.log", timeout=60)
    violated = re.search(r"Invariant (\w+) is violated", log)
    if violated:
        trace = re.findall(r"^State (\d+):", log, re.MULTILINE)
        require(code != 0 and trace, f"Missing TLC failure/trace: {case['cfg']}")
        # TLC numbers the initial state 1; Veil numbers it 0.
        return {"violation": violated[1], "transitions": max(map(int, trace)) - 1}
    counts = re.search(r"[\d,]+ states generated, ([\d,]+) distinct states found, "
                       r"([\d,]+) states left on queue", log)
    require(code == 0 and "Model checking completed. No error has been found." in log
            and counts and int(counts[2].replace(",", "")) == 0,
            f"TLC did not complete: {case['cfg']} (see {directory / 'tlc.log'})")
    return {"distinct": int(counts[1].replace(",", ""))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tla-jar", type=Path, required=True)
    parser.add_argument("--output", type=Path, help="New directory for retained evidence")
    args = parser.parse_args()
    jar = args.tla_jar.resolve()
    require(jar.is_file(), f"Missing TLC jar: {jar}")
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
    else:
        output = Path(tempfile.mkdtemp(prefix="cosmosdb-check-"))
    print(f"Evidence: {output}", flush=True)
    cases = [read_case(path) for path in sorted(HERE.glob("*.cfg"))]
    require(len(cases) == 15, "Expected 15 CFGs; review the validation scope")
    inputs = [HERE / "swscop.tla", HERE / "LICENSE", Path(__file__).resolve(),
              ROOT / "Examples/TLA/CosmosDB.lean", ROOT / "lean-toolchain",
              ROOT / "lake-manifest.json", *(HERE / case["cfg"] for case in cases)]
    hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in inputs}
    hashes["tla2tools.jar"] = hashlib.sha256(jar.read_bytes()).hexdigest()
    (output / "sha256.json").write_text(json.dumps(hashes, indent=2) + "\n")
    check_upstream(output)
    print("Pinned source and license match.", flush=True)
    code, _ = run(["lake", "build", "Examples.TLA.CosmosDB"], ROOT, output / "build.log")
    require(code == 0, f"Translation build failed; see {output / 'build.log'}")
    veil = check_veil(cases, output)
    report = []
    for case in cases:
        tlc = check_tlc(case, jar, output)
        matched = tlc == veil[case["cfg"]]
        report.append({**case, "tlc": tlc, "veil": veil[case["cfg"]], "matched": matched})
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f'{"PASS" if matched else "FAIL"} {case["cfg"]}: {tlc}', flush=True)
    require(all(row["matched"] for row in report), "TLC/Veil mismatch; see report.json")
    print("All 15 cases agree (finite validation, not an equivalence proof).")


if __name__ == "__main__":
    main()
