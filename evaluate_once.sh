#!/bin/sh

python3 ./scripts/eval.py Benchmarks/Veil/ --ivy-dir ./Benchmarks/Ivy/ --output-file evaluate_once.pdf 2> evaluate_once_log.txt | tee evaluate_once_results.txt
mkdir -p /tmp/output
cp evaluate_once_* /tmp/output/