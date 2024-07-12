#! /usr/bin/env python3
import argparse
import sys
import itertools
from typing import Any, Callable, Dict, List, Tuple, TypeAlias, Union
from dataclasses import dataclass
import z3
import pdb

# Dependencies:
# pip3 `install z3-solver cvc5` OR `apt-get install python3-z3 python3-cvc5`

# This program is a wrapper around Z3 that behaves (approximately) like `z3 -in`,
# but overwrites the behaviour of the `(get-model)` command to print the
# model in a more readable format, that can be parsed by our Lean code.
# NOTE: THIS RUNS THE SAT CHECK TWICE! The proper solution would be to
# implement proper Lean bindings for Z3.

parser = argparse.ArgumentParser()
parser.add_argument(
    '--tlimit', help='time limit in seconds', type=int, default=10)

# https://github.com/Z3Prover/z3/issues/1553
# https://stackoverflow.com/questions/63641783/outputting-z3-model-output-in-a-readable-format
# https://github.com/wilcoxjay/mypyvy/blob/3a055dfad3d13fb35b6125ab6f43fa6ea4493b5f/src/translator.py#L460 (`model_to_first_order_structure`)

SortName: TypeAlias = str
DeclName: TypeAlias = str

BoolSort: SortName = 'Bool'
IntSort: SortName = 'Int'


@dataclass(eq=True, frozen=True)
class ConstantDecl:
    name: DeclName
    rng: SortName


@dataclass(eq=True, frozen=True)
class RelationDecl:
    name: DeclName
    dom: Tuple[SortName]


@dataclass(eq=True, frozen=True)
class FunctionDecl:
    name: DeclName
    dom: Tuple[SortName]
    rng: SortName


@dataclass(eq=True, frozen=True)
class UninterpretedValue:
    name: str

    def __repr__(self) -> str:
        return self.name


@dataclass(eq=True, frozen=True)
class SortElement:
    z3expr: z3.ExprRef
    val: Union[bool, UninterpretedValue]

    def __repr__(self) -> str:
        if isinstance(self.val, UninterpretedValue):
            return f"{self.val}"
        else:
            return f"{self.z3expr}"


class Model:
    def __init__(self, z3model: z3.ModelRef):
        print(z3model.sexpr())
        print(z3model)

        # This code almost entirely copy-pasted from mypyvy's `model_to_first_order_structure``
        self.sorts: Dict[str, Any] = {
            BoolSort: [SortElement(z3.BoolVal(True), True), SortElement(z3.BoolVal(False), False)],
            # TODO: do we need Int?
        }

        # collect all z3sorts, including sorts that appear in decls but not in z3model.sorts()
        z3sorts = z3model.sorts()
        z3sort_names = set(s.name() for s in z3sorts) | set(self.sorts.keys())
        for z3decl in sorted(z3model.decls(), key=str):
            for z3sort in [z3decl.domain(i) for i in range(z3decl.arity())] + [z3decl.range()]:
                sortname = z3sort.name()
                if sortname not in z3sort_names:
                    print(
                        f'Found undeclared sort {sortname} in z3decl: {z3decl}', file=sys.stderr)
                    z3sorts.append(z3sort)
                    z3sort_names.add(sortname)

        for z3sort in sorted(z3sorts, key=str):
            sortname = z3sort.name()
            assert sortname not in self.sorts, f"duplicate sort name {sortname}"
            self.sorts[sortname] = []
            univ = z3model.get_universe(z3sort)
            # If the universe is not specified in the model, we add an arbitrary element to it
            # (SMT-LIB assumes all sorts are non-empty, so this is safe to do)
            if univ is None:
                univ = [z3model.eval(
                    z3.Const(f'{sortname}_arbitrary', z3sort), model_completion=True)]
            z3elems = sorted(univ, key=str)
            # self.sorts[sortname] = z3elems
            for i, z3e in enumerate(z3elems):
                e = UninterpretedValue(f'{sortname}{i}')
                self.sorts[sortname].append(SortElement(z3e, e))

        print(self.sorts)

        # Create mapping from (sort, z3expr) to SortElement
        elements: Dict[tuple[SortName, z3.ExprRef], SortElement] = {
            (sortname, z3e): elem
            for sortname, elems in self.sorts.items()
            for elem in elems
            for z3e in [elem.z3expr]
        }

        print(f"Elements: {elements}")

        # interpret constants, relations, and functions
        def _eval_bool(expr: z3.ExprRef) -> bool:
            assert z3.is_bool(expr), expr
            ans = z3model.eval(expr, model_completion=True)
            assert z3.is_bool(ans), (expr, ans)
            return bool(ans)

        def _eval_int(expr: z3.ExprRef) -> int:
            assert z3.is_int(expr), expr
            ans = z3model.eval(expr, model_completion=True)
            assert z3.is_int_value(ans), (expr, ans)
            print(f"_eval_int({expr}) = {ans}")
            return ans.as_long()

        def _eval_elem(sort: SortName) -> Callable[[z3.ExprRef], SortElement]:
            def _eval(expr: z3.ExprRef) -> SortElement:
                assert expr.sort().name(
                ) in self.sorts, f"unknown sort {expr.sort().name()}"
                ans = z3model.eval(expr, model_completion=True)
                assert (
                    sort, ans) in elements, f"unknown element {ans} of sort {sort}; not found in elements {elements}"
                return elements[sort, ans]
            return _eval

        self.decls = {}

        for z3decl in sorted(z3model.decls(), key=str):
            if any(z3decl.domain(i).name() not in self.sorts for i in range(z3decl.arity())):
                assert False, f"decl {z3decl} has unknown sort"
            name = z3decl.name()
            dom = tuple(z3decl.domain(i).name() for i in range(z3decl.arity()))
            rng = z3decl.range().name()
            if len(dom) == 0:
                decl = ConstantDecl(name, rng)
            elif rng == BoolSort:
                decl = RelationDecl(name, dom)
            else:
                decl = FunctionDecl(name, dom, rng)
            self.decls[name] = decl

            _eval: Callable[[z3.ExprRef], Union[bool, int, SortElement]]
            if rng == BoolSort:
                _eval = _eval_bool
            elif rng == IntSort:
                _eval = _eval_int
            else:  # uninterpreted sort
                _eval = _eval_elem(rng)

            domains = [self.sorts[d] for d in dom]
            print(f"domains for {z3decl}: {domains}")
            # Evaluate the const/rel/function on all possible inputs
            fi = {
                row: _eval(z3decl(*(
                    e.z3expr
                    for e in row
                )))
                for row in itertools.product(*domains)
            }
            print(f"fi for {z3decl}: {fi}")

        print(self.decls)

        pdb.set_trace()

    def __str__(self) -> str:
        return f"Model({self.sorts})"


def get_model(passedLines: List[str]) -> Model:
    s = z3.Solver()
    s.from_string("\n".join(passedLines))
    res = s.check()
    assert res == z3.sat, f"Expected sat, got {res}"
    m = s.model()
    print(Model(m))
    # pdb.set_trace()
    return Model(m)


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
