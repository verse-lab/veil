#! /usr/bin/env python3
import argparse
import itertools
import sys
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Tuple, TypeAlias, Union

import sexpdata
import z3

# Dependencies:
# pip3 `install z3-solver cvc5 sexpdata` OR `apt-get install python3-z3 python3-cvc5 python3-sexpdata`

# This program is a wrapper around Z3 that behaves (approximately) like `z3 -in`,
# but overwrites the behaviour of the `(get-model)` command to print the
# model in a more readable format, that can be parsed by our Lean code.
# NOTE: THIS RUNS THE SAT CHECK TWICE! The proper solution would be to
# implement proper Lean bindings for Z3.

parser = argparse.ArgumentParser()
parser.add_argument(
    '--tlimit', help='time limit in seconds', type=int, default=10)

# # https://stackoverflow.com/questions/51286748/make-the-python-json-encoder-support-pythons-new-dataclasses
# class EnhancedJSONEncoder(json.JSONEncoder):
#     def default(self, o):
#         if dataclasses.is_dataclass(o):
#             return dataclasses.asdict(o)
#         if isinstance(o, z3.ExprRef):
#             return str(o)
#         return super().default(o)

# https://github.com/Z3Prover/z3/issues/1553
# https://stackoverflow.com/questions/63641783/outputting-z3-model-output-in-a-readable-format
# https://github.com/wilcoxjay/mypyvy/blob/3a055dfad3d13fb35b6125ab6f43fa6ea4493b5f/src/translator.py#L460 (`model_to_first_order_structure`)

SortName: TypeAlias = str
DeclName: TypeAlias = str

BoolSort: SortName = 'Bool'
IntSort: SortName = 'Int'


def sexp(x: Any) -> str:
    return sexpdata.dumps(x, true_as='true', false_as='false', str_as='symbol')


@dataclass(eq=True, frozen=True)
class ConstantDecl:
    name: DeclName
    rng: SortName

    def __to_lisp_as__(self) -> str:
        return f"(constant {sexp({self.name})} {sexp(self.rng)})"

    def __repr__(self) -> str:
        return self.__to_lisp_as__()


@dataclass(eq=True, frozen=True)
class RelationDecl:
    name: DeclName
    dom: Tuple[SortName]

    def __to_lisp_as__(self) -> str:
        return f"(relation {sexp({self.name})} {sexp(self.dom)})"

    def __repr__(self) -> str:
        return self.__to_lisp_as__()


@dataclass(eq=True, frozen=True)
class FunctionDecl:
    name: DeclName
    dom: Tuple[SortName]
    rng: SortName

    def __to_lisp_as__(self) -> str:
        return f"(function {sexp({self.name})} {sexp(self.dom)} {sexp(self.rng)})"

    def __repr__(self) -> str:
        return self.__to_lisp_as__()


@dataclass(eq=True, frozen=True)
class UninterpretedValue:
    name: str

    def __to_lisp_as__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return self.__to_lisp_as__()


@dataclass(eq=True, frozen=True)
class SortElement:
    z3expr: z3.ExprRef
    val: Union[bool, UninterpretedValue]

    def __to_lisp_as__(self) -> str:
        return f"{sexp(self.val)}"

    def __repr__(self) -> str:
        if isinstance(self.val, UninterpretedValue):
            return f"{self.val}"
        else:
            return f"{self.z3expr}"


@dataclass(eq=True, frozen=True)
class Interpretation:
    decl: Union[ConstantDecl, RelationDecl, FunctionDecl]
    interp: Dict[Tuple, Union[bool, int, SortElement]]

    def __to_lisp_as__(self) -> str:
        strs = []
        strs.append(f"{sexp(self.decl)}")
        for k, v in self.interp.items():
            strs.append(f"(interpret {sexp(self.decl.name)} {sexp(k)} {sexp(v)})")
        return "\n".join(strs)

    def __repr__(self) -> str:
        return self.__to_lisp_as__()


class Model:
    def __to_lisp_as__(self) -> str:
        strs = []
        for sortname, elems in self.sorts.items():
            strs.append(f"(sort {sexp(sortname)} {sexp(elems)})")
        for _declname, interp in self.interps.items():
            strs.append(f"{sexp(interp)}")
        return "(\n" + "\n".join(strs) + "\n)"

    def __repr__(self) -> str:
        return self.__to_lisp_as__()

    def __init__(self, z3model: z3.ModelRef):
        # This code almost entirely copy-pasted from mypyvy's `model_to_first_order_structure``
        self.sorts: Dict[str, Any] = {
            BoolSort: [SortElement(z3.BoolVal(True), True), SortElement(z3.BoolVal(False), False)],
            # IntSort: []
        }

        # collect all z3sorts, including sorts that appear in decls but not in z3model.sorts()
        z3sorts = z3model.sorts()
        z3sort_names = set(s.name() for s in z3sorts) | set(self.sorts.keys())
        for z3decl in sorted(z3model.decls(), key=str):
            collected_sorts = [z3decl.domain(i) for i in range(
                z3decl.arity())] + [z3decl.range()]
            # print(f"collecting z3decl {z3decl} -> {collected_sorts}")
            for z3sort in collected_sorts:
                sortname = z3sort.name()
                if sortname not in z3sort_names:
                    # print(f'Found undeclared sort {sortname} in z3decl: {z3decl}')
                    z3sorts.append(z3sort)
                    z3sort_names.add(sortname)

        # print(f"z3sorts: {z3sorts}")

        for z3sort in sorted(z3sorts, key=str):
            sortname = z3sort.name()
            assert sortname not in self.sorts, f"duplicate sort name {sortname}"
            self.sorts[sortname] = []
            univ = z3model.get_universe(z3sort)
            # print(f"universe for {sortname}: {univ}")
            # NOTE: in the mypyvy version, if `univ` is None, a single unconstrained constant
            # is evaluated to get a value and add it to the universe. I'm not sure why.
            # It might turn out later that we need to do the same.
            if univ is not None:
                z3elems = sorted(univ, key=str)
                for i, z3e in enumerate(z3elems):
                    e = UninterpretedValue(f'{sortname}{i}')
                    self.sorts[sortname].append(SortElement(z3e, e))

        # Create mapping from (sort, z3expr) to SortElement
        elements: Dict[tuple[SortName, z3.ExprRef], SortElement] = {
            (sortname, elem.z3expr): elem
            for sortname, elems in self.sorts.items()
            for elem in elems
        }

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

        self.interps: Dict[DeclName, Interpretation] = {}

        for z3decl in sorted(z3model.decls(), key=str):
            if any(z3decl.domain(i).name() not in self.sorts for i in range(z3decl.arity())):
                assert False, f"decl {z3decl} has unknown sort"
            name: DeclName = z3decl.name()
            dom = tuple(z3decl.domain(i).name() for i in range(z3decl.arity()))
            rng = z3decl.range().name()
            if len(dom) == 0:
                decl = ConstantDecl(name, rng)
            elif rng == BoolSort:
                decl = RelationDecl(name, dom)
            else:
                decl = FunctionDecl(name, dom, rng)

            _eval: Callable[[z3.ExprRef], Union[bool, int, SortElement]]
            if rng == BoolSort:
                _eval = _eval_bool
            elif rng == IntSort:
                _eval = _eval_int
            else:  # uninterpreted sort
                _eval = _eval_elem(rng)

            domains = [self.sorts[d] for d in dom]
            # print(f"domains for {z3decl}: {domains}")
            # Evaluate the const/rel/function on all possible inputs
            fi: Dict[Tuple, Union[bool, int, SortElement]] = {
                row: _eval(z3decl(*(e.z3expr for e in row)))
                for row in itertools.product(*domains)
            }
            # NOTE: mypyvy has some assertions about `fi` here, which we elide
            # print(f"fi for {z3decl}: {fi}")
            self.interps[name] = Interpretation(decl, fi)


def get_model(passedLines: List[str]) -> Model:
    s = z3.Solver()
    s.from_string("\n".join(passedLines))
    res = s.check()
    assert res == z3.sat, f"Expected sat, got {res}"
    m = s.model()
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
