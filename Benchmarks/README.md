# TLC Model Checker Benchmarking Framework

A comprehensive Python framework for systematically measuring the performance of TLC model checking on TLA+ specifications.

## Features

- **Multiple specifications and configurations**: Run benchmarks across many specs with different model sizes
- **Multi-threaded execution**: Test scaling with different worker counts
- **Progress tracking**: Capture TLC's periodic progress reports for detailed analysis
- **Memory monitoring**: Track peak memory consumption via `psutil`
- **Timeout handling**: Gracefully handle long-running or stuck benchmarks
- **Multiple output formats**: JSON (full details), CSV (summary), progress data (for plotting)
- **Visualization**: Generate publication-ready plots for papers

## Installation

### Requirements

- Python 3.7+
- Java 11+ (for TLC)
- `tla2tools.jar` (download from [TLA+ releases](https://github.com/tlaplus/tlaplus/releases))

### Python Dependencies

```bash
# Required
pip install psutil

# For YAML config files
pip install pyyaml

# For plotting
pip install matplotlib numpy
```

### Quick Start

```bash
# Download tla2tools.jar if you don't have it
wget https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar

# Run a single benchmark
python tlc_benchmark.py --spec MySpec.tla --cfg MC.cfg --workers 4

# Run batch benchmarks from config
python tlc_benchmark.py --config benchmark_config.yaml

# Generate plots from results
python plot_results.py benchmark_results/benchmark_results_*.json
```

## Usage

### Single Benchmark

```bash
python tlc_benchmark.py \
    --spec MySpec.tla \
    --cfg MC.cfg \
    --workers 4 \
    --heap 8G \
    --timeout 3600 \
    --reps 3
```

Options:
- `--spec, -s`: TLA+ specification file
- `--cfg`: TLC configuration file
- `--workers, -w`: Number of worker threads (default: 1)
- `--heap`: JVM heap size (default: 4G)
- `--timeout, -t`: Timeout in seconds (default: 3600)
- `--reps, -r`: Number of repetitions (default: 1)
- `--jar`: Path to tla2tools.jar
- `--output, -o`: Output directory
- `--quiet, -q`: Suppress verbose output

### Batch Benchmarks

Create a configuration file (YAML or JSON):

```yaml
# benchmark_config.yaml
global:
  tla2tools_jar: "tla2tools.jar"
  default_timeout: 3600

repetitions: 3

benchmarks:
  - name: "TwoPhase-small"
    spec_file: "specs/TwoPhase.tla"
    config_file: "specs/MC_small.cfg"
    workers: 1
    heap_size: "4G"
    
  - name: "TwoPhase-small-parallel"
    spec_file: "specs/TwoPhase.tla"
    config_file: "specs/MC_small.cfg"
    workers: 4
    heap_size: "4G"
```

Run the batch:

```bash
python tlc_benchmark.py --config benchmark_config.yaml
```

### Configuration Options

Each benchmark entry supports:

| Option | Description | Default |
|--------|-------------|---------|
| `name` | Descriptive name for the benchmark | spec filename |
| `spec_file` | Path to .tla specification | (required) |
| `config_file` | Path to .cfg TLC config | auto-detect |
| `workers` | Number of TLC worker threads | 1 |
| `heap_size` | JVM heap (e.g., "4G", "8G") | "4G" |
| `timeout_seconds` | Max execution time | 3600 |
| `extra_opts` | Additional TLC CLI options | [] |
| `working_dir` | Working directory for TLC | current dir |

## Output

### Directory Structure

```
benchmark_results/
├── benchmark_results_20240115_143022.json    # Full results
├── benchmark_results_20240115_143022.csv     # Summary table
├── benchmark_results_20240115_143022_progress.json  # Progress data
└── intermediate_results.json                  # Checkpoint
```

### JSON Output Schema

```json
{
  "spec_file": "TwoPhase.tla",
  "config_file": "MC.cfg",
  "workers": 4,
  "heap_size": "8G",
  "wall_time_seconds": 125.4,
  "tlc_reported_time": "02min 05s",
  "states_generated": 1568000,
  "distinct_states": 156800,
  "depth": 42,
  "peak_memory_mb": 2048.5,
  "success": true,
  "timeout": false,
  "progress_points": [
    {
      "timestamp": 10.5,
      "states_generated": 50000,
      "distinct_states": 5000,
      "states_in_queue": 3000,
      "memory_mb": 512.3
    }
  ]
}
```

## Plotting Results

### Generate All Plots

```bash
python plot_results.py benchmark_results_*.json
```

### Available Plots

1. **Progress over time** (`_progress.png`)
   - States generated vs time
   - Distinct states vs time
   - Queue size vs time
   - Memory vs time

2. **Throughput** (`_throughput.png`)
   - States per second over time

3. **Comparison bar charts**
   - Execution time (`_time.png`)
   - State space size (`_states.png`)
   - Memory usage (`_memory.png`)

4. **Scaling analysis** (`_scaling.png`)
   - Time vs workers
   - Speedup vs workers (with ideal line)

5. **Summary dashboard** (`_dashboard.png`)
   - Combined overview with all metrics

### Plot Options

```bash
python plot_results.py results.json \
    --output plots \           # Output directory
    --prefix experiment1 \     # Filename prefix
    --progress-only           # Only progress plots
    --comparison-only         # Only comparison plots
```

## Best Practices for Research Experiments

### Reproducibility

1. **Fix JVM heap size**: Set both `-Xms` and `-Xmx` to the same value
2. **Use consistent timeouts**: Set appropriate timeouts for your experiments
3. **Multiple repetitions**: Run at least 3 repetitions to account for variance
4. **Record system info**: The script automatically captures hostname, CPU count
5. **Version control**: Save your config files alongside results

### Hardware Recommendations

```yaml
# For small specs (< 1M states)
workers: 1-4
heap_size: "4G"

# For medium specs (1M - 100M states)  
workers: 4-8
heap_size: "8G-16G"

# For large specs (> 100M states)
workers: 8+
heap_size: "32G+"
```

### Reporting in Papers

Include in your methodology section:
- Machine specifications (CPU, RAM, OS)
- JVM version and settings
- TLC version
- Number of workers
- Timeout used
- Number of repetitions

Example table format:

| Spec | Config | Workers | Time (s) | States | Memory (MB) |
|------|--------|---------|----------|--------|-------------|
| TwoPhase | N=4 | 4 | 125.4 ± 2.1 | 156.8K | 2048 |

## Troubleshooting

### Common Issues

**TLC not found**
```bash
# Check Java installation
java -version

# Verify tla2tools.jar exists
ls -la tla2tools.jar
```

**Out of memory**
```bash
# Increase heap size
python tlc_benchmark.py --spec MySpec.tla --heap 16G
```

**Progress not captured**
- TLC only reports progress periodically (default: every 100K states)
- Very fast benchmarks may complete before first progress report

**psutil not working**
```bash
# Install psutil for memory monitoring
pip install psutil
```

### Getting TLC Progress Reports

TLC reports progress based on state count. For more frequent updates, you can use:

```yaml
extra_opts:
  - "-coverage"
  - "1"  # Report every 1 minute
```

## Integration with Other Tools

### Apalache Comparison

You can create similar benchmarks for Apalache:

```python
# Example: Add Apalache runner to comparison
# See Apalache documentation for CLI usage
```

### CI/CD Integration

```yaml
# GitHub Actions example
- name: Run TLC Benchmarks
  run: |
    python tlc_benchmark.py --config ci_benchmarks.yaml --timeout 300
    python plot_results.py benchmark_results/*.json
```

## References

- [TLC Model Checker Documentation](https://lamport.azurewebsites.net/tla/tlc-options.html)
- [TLA+ Tools Repository](https://github.com/tlaplus/tlaplus)
- [Apalache Symbolic Model Checker](https://github.com/informalsystems/apalache)

## License

MIT License - Feel free to use and modify for your research.
