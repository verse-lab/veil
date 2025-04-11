#!/bin/sh

mkdir -p /tmp/veil-smoke-test
cp -r Benchmarks/Veil/Blockchain.lean Benchmarks/Veil/Ring.lean Benchmarks/Veil/RicartAgrawala.lean Benchmarks/Veil/MultiSigMajority.lean Benchmarks/Veil/TwoPhaseCommit.lean /tmp/veil-smoke-test/
python3 ./scripts/eval.py /tmp/veil-smoke-test/ --ivy-dir ./Benchmarks/Ivy/ --output-file smoke_test.pdf 2> smoke_test_eval_log.txt | tee smoke_test_results.txt
mkdir -p /tmp/output
cp smoke_test_* /tmp/output/