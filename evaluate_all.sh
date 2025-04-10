#!/bin/sh

python3 ./scripts/eval.py Benchmarks/Veil/ --ivy-dir ./Benchmarks/Ivy/ --repeat 5 --output-file evaluate_all.pdf 2> evaluate_all_log.txt | tee evaluate_all_results.txt