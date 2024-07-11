#! /usr/bin/env python3
# pip3 install z3-solver cvc5
# OR apt-get install python3-z3 python3-cvc5
import argparse
import sys
import z3

parser = argparse.ArgumentParser()
parser.add_argument('--tlimit', help='time limit in seconds', type=int, default=10)
parser.add_argument('filename', help='input file (defaults to stdin)', default=sys.stdin, nargs='?')

# https://github.com/Z3Prover/z3/issues/1553
# https://stackoverflow.com/questions/63641783/outputting-z3-model-output-in-a-readable-format

if __name__ == '__main__':
    args = parser.parse_args()
    z3.set_param('timeout', args.tlimit * 1000)
    z3.set_param("unsat_core", True)
    z3.set_param("model", True)
    z3.set_param("model_validate", True)
    # z3.set_param("model.completion", True)

    cfg = z3.Z3_mk_config()
    ctx = z3.Z3_mk_context(cfg)
    
    with open("/tmp/z3.log", "w") as f:
        for line in sys.stdin:
            print(f"{line.strip()}", file=f, flush=True)
            res = z3.Z3_eval_smtlib2_string(ctx, line)
            if len(res) != 0:
                print(res, flush=True)
                print(res, file=f, flush=True)

            if "get-model" in line:
                mo = z3.Z3_mk_model(ctx)
                print(f";; model {mo}", file=f, flush=True)

    sys.exit(1)

