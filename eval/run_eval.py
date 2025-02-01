import subprocess
import re
import argparse
import os
import sys
import numpy as np
import matplotlib.pyplot as plt

# [.*?] [0.129101] try (try dsimp only
# or
# [.*?] [0.124790] dsimp only 
PATTERN_SIMPLIFICATION1 = re.compile(rf"\[.*?\] \[(\d+\.\d+)\] try \(try dsimp only")
PATTERN_SIMPLIFICATION2 = re.compile(rf"          \[Elab\.step\] \[(\d+\.\d+)\] " + '\n' + rf"                dsimp only")

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

def run_file(f: str) -> dict[str, float]:
    f = f.replace("/", ".").removesuffix(".lean")
    print(f"Now running on {f}", file=sys.stderr)
    cmd = ["lake", "build", f]
    output = subprocess.run(cmd, capture_output=True)
    assert output.returncode == 0, f"Failed to run {cmd}: {output.stderr.decode('utf-8')}"
    stdout = output.stdout.decode("utf-8")
    total_query_time = sum(float(it.group(1)) for it in PATTERN_TOTAL_QUERY_TIME.finditer(stdout))
    translation_time = sum(float(it.group(1)) for it in PATTERN_TRANSLATION.finditer(stdout))
    query_time = sum(float(it.group(1)) for it in PATTERN_QUERY.finditer(stdout))
    overall_time = sum(float(it.group(1)) for it in PATTERN_OVERALL.finditer(stdout))
    return {"simplification_time": total_query_time - translation_time - query_time, "translation_time": translation_time, "solving_time": query_time, "total_time": overall_time}

def run_dir(dir: str) -> dict[str, dict[str, float]]:
    ret = {}
    for root, _, files in os.walk(dir):
        print(f"Now running files in {root}", file=sys.stderr)
        if root.startswith("."):
            continue
        for f in files:
            filename = os.path.join(root, f)
            try:
                with open(filename, "r") as file:
                    first_line = file.readline()
                    if "skip eval" in first_line or filename.startswith("."):
                        continue
                ret[filename] = run_file(filename)
            except Exception as e:
                print(f"Failed to run {filename}: {e}", file=sys.stderr)
    return ret

def create_graph(res : dict[str, dict[str, float]], output_file : str):
    categories = {it: it.split("/")[-1].split(".")[0] for it in res.keys()}
    res  = {k: [v["simplification_time"], v["translation_time"], v["solving_time"], v["total_time"]] for k, v in res.items()}
    simp_times = np.array([res[it][0] for it in categories]) # Bottom part of stacked bars
    trans_times = np.array([res[it][1] for it in categories]) # Middle 1 part of stacked bars
    solving_time = np.array([res[it][2] for it in categories]) # Middle 2 part of stacked bars
    x = np.arange(len(categories))  # X-axis positions

    # Plot
    fig, (ax_high, ax_low) = plt.subplots(2, 1, sharex=True, figsize=(8, 6), gridspec_kw={'height_ratios': [2, 1], 'hspace': 0.05})
    ax_low.set_ylim(0, 30)  # Normal range
    ax_high.set_ylim(200, 600)  # Normal range

    ax_low.bar(x, simp_times, width=0.4, label='Simplification Time', color='blue')
    ax_low.bar(x, trans_times, width=0.4, bottom=simp_times, label='Translation Time', color='lightblue')
    ax_low.bar(x, solving_time, width=0.4, bottom=simp_times+trans_times,label='Solver Time', color='green')

    ax_high.bar(x, simp_times, width=0.4, label='Simplification Time', color='blue')
    ax_high.bar(x, trans_times, width=0.4, bottom=simp_times, label='Translation Time', color='lightblue')
    ax_high.bar(x, solving_time, width=0.4, bottom=simp_times+trans_times,label='Solver Time', color='green')

    # Add text for time on top of the bars
    for it in range(len(categories)):
        time = solving_time[it] + trans_times[it] + simp_times[it]
        text = str(time)
        text = text if len(text) < 5 else text[:4]
        if time + 1 <= 30:
            ax_low.text(x[it], time + 1, text, fontsize=11, color='black', ha='center', rotation=90)
        ax_high.text(x[it], 2 + time, text, fontsize=11, color='black', ha='center', rotation=90)

    # Add diagonal break marks
    d = 0.015  # Adjust diagonal size
    kwargs = dict(transform=ax_high.transAxes, color='k', clip_on=False)

    # Top break marks (ax_high → lower boundary)
    ax_high.plot((-d, +d), (-d, +d), **kwargs)  
    ax_high.plot((1 - d, 1 + d), (-d, +d), **kwargs)  

    kwargs = dict(transform=ax_low.transAxes, color='k', clip_on=False)

    # Bottom break marks (ax_low → upper boundary)
    ax_low.plot((-d, +d), (1 - d, 1 + d), **kwargs)  
    ax_low.plot((1 - d, 1 + d), (1 - d, 1 + d), **kwargs)  

    # Labels & Legend
    ax_low.spines['top'].set_visible(False)
    ax_high.spines['bottom'].set_visible(False)
    ax_low.set_xticks(x)
    ax_high.tick_params(axis='x', top=False, bottom=False, labelbottom=False)
    plt.xticks(rotation=30, ha='right')
    ax_low.set_xticklabels(list(categories.values()))
    ax_low.set_ylabel("Normalised time")
    ax_high.legend(prop={'size': 14}, loc=1, ncol=2)

    plt.savefig(output_file, dpi=300, bbox_inches='tight')

# NOTE: Requires the benchmarks to have `set_option trace.profiler true`.
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", type=str)
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--output-file", type=str, default=None)
    args = parser.parse_args()
    if args.repeat < 1:
        exit(1)
    if os.path.isdir(args.input_file):
        results : list[dict[str, dict[str, float]]] = []
        for i in range(args.repeat):
            if args.repeat > 1:
                print(f"Running for the {i + 1}th time", file=sys.stderr)
            results.append(run_dir(args.input_file))
        # average the results
        averaged_results = {}
        for file in results[0]:
            averaged_results[file] = {j: sum(res[file][j] for res in results) / args.repeat 
                                        for j in {"simplification_time", "translation_time", "solving_time", "total_time"}}
        if args.output_file:
            create_graph(averaged_results, args.output_file)
        else:
            print(averaged_results)
    else:
        if args.output_file:
            print("Cannot create graph for one benchmark.", file=sys.stderr)
            exit(1)
        results : list[dict[str, float]] = []
        for i in range(args.repeat):
            if args.repeat > 1:
                print(f"Running for the {i + 1}th time", file=sys.stderr)
            results.append(run_file(args.input_file))
        # average the results
        averaged_results = {j: sum(res[j] for res in results) / args.repeat for j in {"simplification_time", "translation_time", "solving_time", "total_time"}}
        print(averaged_results)
