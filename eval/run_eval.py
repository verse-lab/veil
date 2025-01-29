import subprocess
import re
import argparse
import os
import sys

# [.*?] [0.129101] try (try dsimp only
# or
# [.*?] [0.124790] dsimp only 
PATTERN_SIMPLIFICATION1 = re.compile(rf"\[.*?\] \[(\d+\.\d+)\] try \(try dsimp only")
PATTERN_SIMPLIFICATION2 = re.compile(rf"          \[Elab\.step\] \[(\d+\.\d+)\] {'\n'}                dsimp only")

# [Elab.step] [0.162373] solve_clause
# or
# [Elab.step] [0.162373] solve_wlp_clause
PATTERN_TOTAL_QUERY_TIME = re.compile(r"        \[Elab\.step\] \[(\d+\.\d+)\] solve_(?:wlp_)?clause")

# [sauto.perf.translate] [0.018582] prepareAutoQuery
PATTERN_TRANSLATION = re.compile(r"\[sauto\.perf\.translate\] \[(\d+\.\d+)\] prepareAutoQuery")

# [sauto.perf.query] [0.067984] querySolver
PATTERN_QUERY = re.compile(r"\[sauto\.perf\.query\] \[(\d+\.\d+)\] querySolver")

# [Elab.command] [0.145319] @[invProof]
PATTERN_OVERALL = re.compile(r": \[Elab\.command\] \[(\d+\.\d+)\] @\[invProof\]")
def run_file(f: str) -> tuple[float, float, float, float]:
    f = f.replace("/", ".").removesuffix(".lean")
    print(f"Now running on {f}", file=sys.stderr)
    cmd = ["lake", "build", f]
    output = subprocess.run(cmd, capture_output=True)
    assert output.returncode == 0, f"Failed to run {cmd}: {output.stderr.decode('utf-8')}"
    stdout = output.stdout.decode("utf-8")
    with open(f"logs/{f}.log", "w") as file:
        file.write(stdout)
    # simplification_time = sum(float(it.group(1)) for it in PATTERN_SIMPLIFICATION1.finditer(stdout))
    # simplification_time += sum(float(it.group(1)) for it in PATTERN_SIMPLIFICATION2.finditer(stdout))
    # simplification time is quite annoying to compute accurately
    total_query_time = sum(float(it.group(1)) for it in PATTERN_TOTAL_QUERY_TIME.finditer(stdout))
    translation_time = sum(float(it.group(1)) for it in PATTERN_TRANSLATION.finditer(stdout))
    query_time = sum(float(it.group(1)) for it in PATTERN_QUERY.finditer(stdout))
    overall_time = sum(float(it.group(1)) for it in PATTERN_OVERALL.finditer(stdout))
    return total_query_time - translation_time - query_time, translation_time, query_time, overall_time

def run_dir(dir: str) -> dict[str, tuple[float, float, float]]:
    ret = {}
    for root, _, files in os.walk(dir):
        print(f"Now running files in {root}", file=sys.stderr)
        for f in files:
            filename = os.path.join(root, f)
            with open(filename, "r") as file:
                first_line = file.readline()
                if "skip_eval" in first_line:
                    continue
            ret[filename] = run_file(filename)
    return ret

# NOTE: Requires the benchmarks to have `set_option trace.profiler true`.
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dir", type=str)
    args = parser.parse_args()
    print(run_dir(args.dir))