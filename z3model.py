#! /usr/bin/env python3
import argparse
import sys
from typing import List
import z3

# Dependencies:
# pip3 `install z3-solver cvc5` OR `apt-get install python3-z3 python3-cvc5`

# This program is a wrapper around Z3 that behaves (approximately) like `z3 -in`,
# but overwrites the behaviour of the `(get-model)` command to print the
# model in a more readable format, that can be parsed by our Lean code.
# NOTE: THIS RUNS THE SAT CHECK TWICE! The proper solution would be to
# implement proper Lean bindings for Z3.

parser = argparse.ArgumentParser()
parser.add_argument('--tlimit', help='time limit in seconds', type=int, default=10)

# https://github.com/Z3Prover/z3/issues/1553
# https://stackoverflow.com/questions/63641783/outputting-z3-model-output-in-a-readable-format
# https://github.com/wilcoxjay/mypyvy/blob/3a055dfad3d13fb35b6125ab6f43fa6ea4493b5f/src/translator.py#L460 (`model_to_first_order_structure`)

def get_model(passedLines: List[str]):
    s = z3.Solver()
    s.from_string("\n".join(passedLines))
    res = s.check()
    if res == z3.sat:
        m = s.model()
        return m

if __name__ == '__main__':
    args = parser.parse_args()
    z3.set_param('timeout', args.tlimit * 1000)
    z3.set_param("unsat_core", True)
    z3.set_param("model", True)
    z3.set_param("model_validate", True)
    z3.set_param("model.completion", True)

    cfg = z3.Z3_mk_config()
    ctx = z3.Z3_mk_context(cfg)
    
    # lines we've passed to Z3 thus far
    passedLines = []

    # For debugging; TODO: remove
    with open("/tmp/z3.log", "w") as f:
        for line in sys.stdin:
            print(f"{line.strip()}", file=f, flush=True)
            # Overwrite the behaviour of `(get-model)` to print the model in a more readable format
            if "(get-model)" in line:
                m = get_model(passedLines)
                print(m, flush=True)
                print(m, file=f, flush=True)
            # Execute all other commands as usual
            else:
                res = z3.Z3_eval_smtlib2_string(ctx, line)
                passedLines.append(line)
                if len(res) != 0:
                    print(res, flush=True)
                    print(res, file=f, flush=True)

    sys.exit(1)