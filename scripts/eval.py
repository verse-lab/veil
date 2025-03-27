import collections
import subprocess
import re
import argparse
import os
import sys
import numpy as np
import matplotlib.pyplot as plt
import time

# [veil.smt.perf.solveClause] [0.053585]
PATTERN_TOTAL_TACTIC_TIME = re.compile(r"\[veil\.smt\.perf\.solveClause\] \[(\d+\.\d+)\]")

# [veil.smt.perf.translate] [0.018582]
PATTERN_TRANSLATION = re.compile(r"\[veil\.smt\.perf\.translate\] \[(\d+\.\d+)\] prepareAutoQuery")

# [veil.smt.perf.query] [0.067984]
PATTERN_QUERY = re.compile(r"\[veil\.smt\.perf\.query\] \[(\d+\.\d+)\] querySolver")

# [0.145319] #check_invariants
PATTERN_OVERALL = re.compile(r"\[veil\.perf\.checkInvariants\] \[(\d+\.\d+)\] checkInvariants")


EXTRA_IVY_ARGS = {
    "PaxosFirstOrder.ivy": ["complete=fo"],
    "SuzukiKasamiInts.ivy": ["complete=fo"],
    "VerticalPaxosFirstOrder.ivy": ["complete=fo"],
    # as recommended in the [instructions](https://github.com/haochenpan/rabia/blob/main/proofs/README)
    # the `isolate=protocol` corresponds to checking just what we have ported to Veil
    "Rabia.ivy": ["seed=1", "isolate=protocol"],
}

def run_ivy(lean_file: str) -> dict[str, float]:
    base_name = os.path.basename(lean_file).replace(".lean", ".ivy")
    ivy_path = os.path.join(args.ivy_dir, base_name)
    print(f"Running ivy_check on {ivy_path} (and measuring total runtime)", file=sys.stderr)
    extra_args = EXTRA_IVY_ARGS.get(base_name, [])
    cmd = ["ivy_check"] + extra_args + [ivy_path]
    ivy_start = time.monotonic()
    output = subprocess.run(cmd, capture_output=True)
    ivy_end = time.monotonic()
    assert output.returncode == 0, f"Failed to run {cmd}: {output.stderr.decode('utf-8')}"
    total_ivy_time = ivy_end - ivy_start
    return {"total_ivy_time": total_ivy_time}

def run_file(filepath: str) -> dict[str, float]:
    ivy_res = run_ivy(filepath)
    print(f"Running Lean on{filepath} (and measuring #check_invariants)", file=sys.stderr)
    # IMPORTANT: `lake build` does nothing on repeat, so we use `lake lean` instead
    # leanModPath = f.replace("/", ".").removesuffix(".lean"); cmd = ["lake", "build", leanModPath]
    cmd = ["lake", "lean", filepath, "--", "-Dweak.veil.perf.profile.checkInvariants=true"]
    output = subprocess.run(cmd, capture_output=True)
    assert output.returncode == 0, f"Failed to run {cmd}: {output.stderr.decode('utf-8')}"
    stdout = output.stdout.decode("utf-8")
    print(stdout, file=sys.stderr)
    total_tactic_time = sum(float(it.group(1)) for it in PATTERN_TOTAL_TACTIC_TIME.finditer(stdout))
    translation_time = sum(float(it.group(1)) for it in PATTERN_TRANSLATION.finditer(stdout))
    query_time = sum(float(it.group(1)) for it in PATTERN_QUERY.finditer(stdout))
    overall_time = sum(float(it.group(1)) for it in PATTERN_OVERALL.finditer(stdout))
    # The following definition would only consider the 'actual' simplification time:
    # simplification_time = total_tactic_time - translation_time - query_time

    # To make the sums add up to the overall time, however, we define
    # 'simplification' time to include all the operations that are not
    # translation from Lean to SMT-LIB and solver invocation.
    simplification_time = overall_time - translation_time - query_time
    veil_res = {"simplification_time": simplification_time, "translation_time": translation_time, "solving_time": query_time, "total_time": overall_time}
    return {**veil_res, **ivy_res}

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
                    if "skip eval" in first_line or filename.startswith(".") or (not filename.endswith("lean")):
                        continue
                ret[filename] = run_file(filename)
            except Exception as e:
                print(f"Failed to run {filename}: {e}", file=sys.stderr)
    return ret

def create_graphs(res : dict[str, dict[str, float]], output_file : str):
    categories = {it: it.split("/")[-1].split(".")[0] for it in res.keys()}
    res  = {k: [v["simplification_time"], v["translation_time"], v["solving_time"], v["total_time"], v["total_ivy_time"]] for k, v in res.items()}
    simp_times = np.array([res[it][0] for it in categories]) # Bottom part of stacked bars
    trans_times = np.array([res[it][1] for it in categories]) # Middle part of stacked bars
    solving_times = np.array([res[it][2] for it in categories]) # Top part of stacked bars
    total_times = np.array([res[it][3] for it in categories]) # Total time (should be sum of the previous three)
    ivy_times = np.array([res[it][4] for it in categories]) # Separate bar for Ivy
    x = np.arange(len(categories))  # X-axis positions

    def create_raw_graph(output_file : str):
        fig, (ax_high, ax_low) = plt.subplots(2, 1, sharex=True, figsize=(8, 6), gridspec_kw={'height_ratios': [2, 1], 'hspace': 0.05})
        ax_low.set_ylim(0, 30)  # Normal range
        ax_high.set_ylim(200, 600)  # Normal range

        ax_low.bar(x - 0.2, simp_times, width=0.4, label='Simplification Time', color='blue')
        ax_low.bar(x - 0.2, trans_times, width=0.4, bottom=simp_times, label='Translation Time', color='lightblue')
        ax_low.bar(x - 0.2, solving_times, width=0.4, bottom=simp_times+trans_times,label='Solver Time', color='green')
        ax_low.bar(x + 0.2, ivy_times, width=0.4, label='Ivy Runtime', color='red')

        ax_high.bar(x - 0.2, simp_times, width=0.4, label='Simplification Time', color='blue')
        ax_high.bar(x - 0.2, trans_times, width=0.4, bottom=simp_times, label='Translation Time', color='lightblue')
        ax_high.bar(x - 0.2, solving_times, width=0.4, bottom=simp_times+trans_times,label='Solver Time', color='green')
        ax_high.bar(x + 0.2, ivy_times, width=0.4, label='Ivy Runtime', color='red')

        # Add text for time on top of the bars
        for it in range(len(categories)):
            # Veil runtimes
            time = total_times[it]
            text = str(time)
            text = text if len(text) < 5 else text[:4]
            if time + 1 <= 30:
                ax_low.text(x[it] - 0.2, time + 1, text, fontsize=11, color='black', ha='center', rotation=90)
            ax_high.text(x[it] - 0.2, 2 + time, text, fontsize=11, color='black', ha='center', rotation=90)

            # Ivy runtimes
            time = ivy_times[it]
            text = str(time)
            text = text if len(text) < 5 else text[:4]
            ax_low.text(x[it] + 0.2, time + 1, text, fontsize=11, color='black', ha='center', rotation=90)

        for idx, v in enumerate(ivy_times):
            if v > 0: continue
            text = '*' if v == 0 else '†'
            ax_low.text(x[idx] + 0.2, 0.2, text, fontsize=14, color='black', ha='center')

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
        ax_low.set_ylabel("Time (s)")
        ax_high.legend(prop={'size': 14}, loc=1, ncol=2)

        plt.savefig(output_file, dpi=300, bbox_inches='tight')

    def create_normalized_graph(output_file : str):
        simp_times_normalized = np.array([(simp_times[it]) / (total_times[it]) for it in range(len(categories))])
        trans_times_normalized = np.array([trans_times[it] / (total_times[it]) for it in range(len(categories))])
        solving_time_normalized = np.array([solving_times[it] / (total_times[it]) for it in range(len(categories))])
        ivy_times_normalized = np.array([ivy_times[it] / (total_times[it]) for it in range(len(categories))])

        fig, (ax_high, ax_low) = plt.subplots(2, 1, sharex=True, figsize=(12, 6), gridspec_kw={'height_ratios': [1, 4], 'hspace': 0.05})
        ax_low.set_ylim(0, 3)  # Normal range
        ax_high.set_ylim(7, 10)  # Normal range

        ax_high.bar(x - 0.2, simp_times_normalized, width=0.4, label='Simplification Time', color='blue')
        ax_high.bar(x - 0.2, trans_times_normalized, width=0.4, bottom=simp_times_normalized, label='Translation Time', color='lightblue')
        ax_high.bar(x - 0.2, solving_time_normalized, width=0.4, bottom=simp_times_normalized+trans_times_normalized, label='Solver Time', color='green')
        ax_high.bar(x + 0.2, ivy_times_normalized, width=0.4, label='Ivy Runtime', color='red')

        ax_low.bar(x - 0.2, simp_times_normalized, width=0.4, label='Simplification Time', color='blue')
        ax_low.bar(x - 0.2, trans_times_normalized, width=0.4, bottom=simp_times_normalized, label='Translation Time', color='lightblue')
        ax_low.bar(x - 0.2, solving_time_normalized, width=0.4, bottom=simp_times_normalized+trans_times_normalized,label='Solver Time', color='green')
        ax_low.bar(x + 0.2, ivy_times_normalized, width=0.4, label='Ivy Runtime', color='red')

        for idx, v in enumerate(ivy_times_normalized):
            if v > 0: continue
            text = '*' if v == 0 else '†'
            ax_low.text(x[idx] + 0.2, 0.2, text, fontsize=14, color='black', ha='center')

        for it in range(len(categories)):
            text = str(total_times[it])
            text = text if len(text) < 5 else text[:4]
            ax_low.text(x[it] - 0.2, 1.2, text, fontsize=11, color='black', ha='center', rotation=90)
            ivy_time_text = str(ivy_times[it])
            ivy_time_text = ivy_time_text if len(ivy_time_text) < 5 else ivy_time_text[:4]
            if ivy_times[it] > 0:
                if ivy_times_normalized[it] + 0.2 <= 3:
                    ax_low.text(x[it] + 0.28, ivy_times_normalized[it] + 0.2, ivy_time_text, fontsize=11, color='black', ha='center', rotation=90)
                ax_high.text(x[it] + 0.28, ivy_times_normalized[it] + 0.2, ivy_time_text, fontsize=11, color='black', ha='center', rotation=90)

        # Labels & Legend
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

        ax_low.spines['top'].set_visible(False)
        ax_high.spines['bottom'].set_visible(False)

        ax_low.set_xticks(x)
        ax_high.tick_params(axis='x', top=False, bottom=False, labelbottom=False)
        plt.xticks(rotation=30, ha='right')
        ax_low.set_xticklabels(categories)
        ax_low.set_ylabel("Normalised time")
        # ax_high.set_title("Results for RQ1")
        ax_high.legend(prop={'size': 14}, loc=1, ncol=2)

        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        
    
    raw_filename = os.path.basename(output_file).replace(".", "_raw.")
    create_raw_graph(raw_filename)

    normalized_filename = os.path.basename(output_file).replace(".", "_normalized.")
    create_normalized_graph(normalized_filename)

# NOTE: Requires the benchmarks to have `set_option trace.profiler true`.
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", type=str)
    parser.add_argument("--ivy-dir", type=str, default='Examples/Ivy', help="directory including Ivy specifications corresponding to the Lean ones (default: `Examples/Ivy`)")
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
                                        for j in {"simplification_time", "translation_time", "solving_time", "total_time", "total_ivy_time"}}
        print(dict(sorted(averaged_results.items())))
        if args.output_file:
            create_graphs(averaged_results, args.output_file)
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
        averaged_results = {j: sum(res[j] for res in results) / args.repeat for j in {"simplification_time", "translation_time", "solving_time", "total_time", "total_ivy_time"}}
        averaged_results = dict(sorted(averaged_results.items()))
        print(averaged_results)