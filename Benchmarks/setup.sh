#!/bin/bash
# TLC Benchmark Setup Script
# 
# This script downloads TLC and installs Python dependencies

set -e

echo "======================================"
echo "TLC Benchmarking Framework Setup"
echo "======================================"

# Verify Java
echo ""
echo "Checking Java..."
java -version 2>&1 | head -1

# I'm using f0fd12a, 1.8.0, sha256:3f098b9c9a2adc34763a7700390fdd6b975cc296d34f760f2e9633ba6dff33c5

# Test TLC
echo ""
echo "Testing TLC..."
java -jar tla2tools.jar -h 2>&1 | head -5

# Create example spec for testing
echo ""
echo "Creating test specification..."
mkdir -p setup-test-specs

cat > setup-test-specs/TestSpec.tla << 'EOF'
---- MODULE TestSpec ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 10

Spec == Init /\ [][Next]_x

Inv == x >= 0 /\ x < 10
====
EOF

cat > setup-test-specs/TestSpec.cfg << 'EOF'
SPECIFICATION Spec
INVARIANT Inv
EOF

echo ""
echo "======================================"
echo "Setup complete!"
echo "======================================"
echo ""
echo "Quick test:"
echo "  python3 tlc_benchmark.py --spec setup-test-specs/TestSpec.tla --cfg setup-test-specs/TestSpec.cfg"
echo ""
echo "Full benchmark:"
echo "  python3 tlc_benchmark.py --config benchmark_config.yaml"
echo ""
echo "Generate plots:"
echo "  python3 plot_results.py benchmark_results/*.json"
