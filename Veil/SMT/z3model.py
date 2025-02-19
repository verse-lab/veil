#! /usr/bin/env python3

# This program is a wrapper around Z3 that behaves (approximately) like `z3 -in`,
# but overwrites the behaviour of the `(get-model)` command to print the
# model in a more readable format, that can be parsed by our Lean code.

# https://github.com/Z3Prover/z3/issues/1553
# https://stackoverflow.com/questions/63641783/outputting-z3-model-output-in-a-readable-format
# https://github.com/wilcoxjay/mypyvy/blob/3a055dfad3d13fb35b6125ab6f43fa6ea4493b5f/src/translator.py#L460 (`model_to_first_order_structure`)

import argparse
import itertools
import sys
import time
from contextlib import contextmanager
from dataclasses import dataclass
from typing import (Any, Callable, Dict, Iterable, Iterator, List, Optional,
                    Set, Tuple, TypeAlias, Union, cast)

import multiprocess as mp
import sexpdata
import z3

SortName: TypeAlias = str
DeclName: TypeAlias = str
BoolSort: SortName = 'Bool'
IntSort: SortName = 'Int'

# We use this prefix to identify variables artificially introduced to
# represent the cardinality of a sort for minimization.
CARDINALITY_VAR_PREFIX = "_card$_"

# We give up enumerating integer in the domain of a relation after this
# many, and simply display the AST of the interpretation.
MAXIMUM_DOMAIN_INTEGERS_TO_ENUMERATE=5

parser = argparse.ArgumentParser()
parser.add_argument(
    '--minimize', help='minimize the model', action='store_true')
parser.add_argument(
    '--tlimit', help='time limit in milliseconds', type=int, default=10000)
parser.add_argument(
    '--seed', help='seed for SMT solver', type=int, default=0xcafe)
parser.add_argument(
    '--log', help='SMT query log file', type=argparse.FileType('a'), default=None)


def sexp(x: Any) -> str:
    return sexpdata.dumps(x, true_as='true', false_as='false', str_as='symbol')

@dataclass(eq=True, frozen=True)
class ConstantDecl:
    name: DeclName
    rng: SortName

    def __to_lisp_as__(self) -> str:
        return f"(constant |{self.name}| {sexp(self.rng)})"

    def __repr__(self) -> str:
        return self.__to_lisp_as__()


@dataclass(eq=True, frozen=True)
class RelationDecl:
    name: DeclName
    dom: Tuple[SortName]

    def __to_lisp_as__(self) -> str:
        return f"(relation |{self.name}| {sexp(self.dom)})"

    def __repr__(self) -> str:
        return self.__to_lisp_as__()


@dataclass(eq=True, frozen=True)
class FunctionDecl:
    name: DeclName
    dom: Tuple[SortName]
    rng: SortName

    def __to_lisp_as__(self) -> str:
        return f"(function |{self.name}| {sexp(self.dom)} {sexp(self.rng)})"

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
    val: Union[bool, int, UninterpretedValue]

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
    explicitInterpretation: Dict[Tuple, Union[bool, int, SortElement]]
    symbolicInterpretation: Optional[str] = None

    def is_cardinality_related(self) -> bool:
        return CARDINALITY_VAR_PREFIX in self.decl.name

    def __to_lisp_as__(self) -> str:
        strs = []
        strs.append(f"{sexp(self.decl)}")
        if self.symbolicInterpretation is not None:
            strs.append(f"(symbolic |{self.decl.name}| |{sexp(self.symbolicInterpretation)}|)")
        else:
            for k, v in self.explicitInterpretation.items():
                strs.append(f"(interpret |{self.decl.name}| {sexp(k)} {sexp(v)})")
        return "\n".join(strs)

    def __repr__(self) -> str:
        return self.__to_lisp_as__()


class Model:
    def __to_lisp_as__(self) -> str:
        strs = []
        for sortname, elems in self.sorts.items():
            strs.append(f"(sort |{sortname}| {sexp(elems)})")
        real_interps = filter(lambda x: not x[1].is_cardinality_related(), self.interps.items())
        for _declname, interp in real_interps:
            strs.append(f"{sexp(interp)}")
        return "(\n" + "\n".join(strs) + "\n)"

    def __repr__(self) -> str:
        return self.__to_lisp_as__()

    def translateASTString(self, ast: str) -> str:
        """Applies the translations in `self.fromZ3ElemToSortElemName`
        to the given AST string"""
        for z3elem, elemname in self.fromZ3ElemToSortElemName.items():
            ast = ast.replace(str(z3elem), elemname)
        return ast

    def __init__(self, z3model: z3.ModelRef):
        self.fromZ3ElemToSortElemName: Dict[z3.ExprRef, str] = {}
        # This code largely copy-pasted from mypyvy's `model_to_first_order_structure``
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

        # print(f"z3sorts: {z3sorts}", file=sys.stderr)
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
                    elemname = f'{sortname}{i}'
                    self.fromZ3ElemToSortElemName[z3e] = elemname
                    e = UninterpretedValue(elemname)
                    self.sorts[sortname].append(SortElement(z3e, e))

        # Create mapping from (sort, z3expr) to SortElement
        elements: Dict[tuple[SortName, z3.ExprRef], SortElement] = {
            (sortname, elem.z3expr): elem
            for sortname, elems in self.sorts.items()
            for elem in elems
        }

        # interpret constants, relations, and functions
        def _eval_bool(expr: z3.ExprRef) -> Union[bool, None]:
            assert z3.is_bool(expr), expr
            ans = z3model.eval(expr, model_completion=True)
            assert z3.is_bool(ans), (expr, ans)
            return bool(ans) if z3.is_false(ans) or z3.is_true(ans) else None

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

            # print(f"Processing decl {z3decl}", file=sys.stderr)
            name: DeclName = z3decl.name()
            dom = tuple(z3decl.domain(i).name() for i in range(z3decl.arity()))
            rng = z3decl.range().name()
            decl: Union[ConstantDecl, RelationDecl, FunctionDecl]
            if len(dom) == 0:
                decl = ConstantDecl(name, rng)
            elif rng == BoolSort:
                decl = RelationDecl(name, dom)
            else:
                decl = FunctionDecl(name, dom, rng)

            symbolicInterpretation = None
            # For relations with arguments of type `Int`, we use the following
            # to identify which integers the relation is true for, and we add
            # these to the universe of the `Int` sort.
            if isinstance(decl, RelationDecl) and any(d == IntSort for d in dom):
                # dtype = " -> ".join(dom)
                # print(f"  Getting Int domain for {z3decl} : {dtype}", file=sys.stderr)
                (int_domain, ast) = get_int_domain(z3decl, z3model)
                # A finite (< MAXIMUM_DOMAIN_INTEGERS_TO_ENUMERATE) domain is returned as a set of integers
                if ast is None:
                    elem_int_domain = {SortElement(z3.IntVal(i), i) for i in int_domain}
                    self.sorts[IntSort] = set(self.sorts[IntSort]) | elem_int_domain
                else:
                    symbolicInterpretation = self.translateASTString(str(ast))

            if symbolicInterpretation is not None:
                self.interps[name] = Interpretation(decl, {}, symbolicInterpretation)
            else:
                _eval: Callable[[z3.ExprRef], Union[bool, int, SortElement, None]]
                if rng == BoolSort:
                    _eval = _eval_bool
                elif rng == IntSort:
                    _eval = _eval_int
                else:  # uninterpreted sort
                    _eval = _eval_elem(rng)

                domains = [self.sorts[d] for d in dom]
                # print(f"domains for {z3decl}: {domains}", file=sys.stderr)
                # Evaluate the const/rel/function on all possible inputs
                fi: Dict[Tuple, Union[bool, int, SortElement]] = {
                    row: evaluated
                    for row in itertools.product(*domains)
                    if (evaluated := _eval(z3decl(*(e.z3expr for e in row))))
                }
                # NOTE: mypyvy has some assertions about `fi` here, which we elide
                # print(f"fi for {z3decl}: {fi}")
                self.interps[name] = Interpretation(decl, fi, None)


def get_int_domain(z3decl: z3.FuncDeclRef, z3model: z3.ModelRef) -> tuple[Set[int], Any]:
    """Given a Z3 function declaration with range Bool (i.e. a
    relation), returns the set of integer arguments for which there
    exist arguments that make the relation true."""
    assert z3decl.range().name(
    ) == BoolSort, f"expected relation, but {z3decl} has range {z3decl.range().name()}"
    args = [z3.Const(f"arg{i}", z3decl.domain(i)) for i in range(z3decl.arity())]
    # sorts = [arg.sort().name() for arg in args]
    int_args = [arg for arg in args if arg.sort().name() == IntSort]
    # print(f"{z3decl} | args: {args} | sort:s {sorts}", file=sys.stderr)

    interp = z3model.eval(z3.Lambda(args, z3decl(*args)),
                          model_completion=True)
    # print(f"interp: {interp}", file=sys.stderr)
    print(args)
    # vp = z3.simplify(interp.__getitem__(*args))
    vp = z3.simplify(interp[*args])
    solver = z3.Solver()
    solver.add(vp)

    int_domain = set()
    num_iterations = 0
    while solver.check() == z3.sat and num_iterations < MAXIMUM_DOMAIN_INTEGERS_TO_ENUMERATE:
        m = solver.model()
        num_iterations += 1
        # print(f"Blocking model {m}", file=sys.stderr)
        # Collect the integer values that make the relation true
        for arg in int_args:
            v = m.eval(arg)
            if isinstance(v, z3.IntNumRef):
                int_domain.add(v.as_long())
            else:
                # George: I think this means the relation is true for all arguments?
                print(f"expected to get integer from m.eval({arg}), got {v} (of type {type(v)})", file=sys.stderr)
        # Ignore this tuple of integers
        solver.add(z3.And(*[arg != m.eval(arg) for arg in int_args]))

    if num_iterations >= MAXIMUM_DOMAIN_INTEGERS_TO_ENUMERATE:
        print(f"Warning: too many integers in domain of {z3decl}, returning AST of interpretation:\n{interp}", file=sys.stderr)
        return int_domain, interp
    else:
        return int_domain, None


def _cardinality_constraint(x: Union[z3.SortRef, z3.FuncDeclRef], n: int) -> z3.ExprRef:
    if isinstance(x, z3.SortRef):
        return _sort_cardinality_constraint(x, n)
    else:
        return _relational_cardinality_constraint(x, n)

def _sort_cardinality_constraint(s: z3.SortRef, n: int) -> z3.ExprRef:
    x = z3.Const(f'{CARDINALITY_VAR_PREFIX}x$', s)
    disjs = []
    for i in range(n):
        c = z3.Const(f'{CARDINALITY_VAR_PREFIX}{s.name()}_{i}', s)
        disjs.append(x == c)

    return z3.ForAll(x, z3.Or(*disjs))

def _relational_cardinality_constraint(relation: z3.FuncDeclRef, n: int) -> z3.ExprRef:
    if relation.arity() == 0:
        return z3.BoolVal(True)

    consts = [[z3.Const(f'{CARDINALITY_VAR_PREFIX}{relation}_{i}_{j}', relation.domain(j))
                for j in range(relation.arity())]
                for i in range(n)]

    vs = [z3.Const(f'{CARDINALITY_VAR_PREFIX}x$_{relation}_{j}', relation.domain(j)) for j in range(relation.arity())]

    result = z3.ForAll(vs, z3.Implies(relation(*vs), z3.Or(*(
        z3.And(*(
            c == v for c, v in zip(cs, vs)
        ))
        for cs in consts
    ))))
    return result

@contextmanager
def new_frame(s : z3.Solver) -> Iterator[None]:
    s.push()
    yield None
    s.pop()

def _minimal_model(s : z3.Solver, sorts_to_minimize: Iterable[z3.SortRef], relations_to_minimize: Iterable[z3.FuncDeclRef],) -> z3.ModelRef:
    with new_frame(s):
        for x in itertools.chain(
                cast(Iterable[Union[z3.SortRef, z3.FuncDeclRef]], sorts_to_minimize),
                relations_to_minimize):
            for n in itertools.count(start=1):
                with new_frame(s):
                    s.add(_cardinality_constraint(x, n))
                    res = s.check()
                    assert res in (z3.sat, z3.unsat), res
                    if res == z3.sat:
                        break
            s.add(_cardinality_constraint(x, n))

        assert s.check() == z3.sat
        return s.model()


def get_model(passedLines: List[str]) -> Model:
    s = z3.Solver()
    s.from_string("\n".join(passedLines))
    res = s.check()
    assert res == z3.sat, f"Expected sat, got {res} (reason: {s.reason_unknown()})"
    m = s.model()
    if args.minimize:
        m = _minimal_model(s, m.sorts(), m.decls())
    print(f"Model: {m}", file=sys.stderr)
    return Model(m)

def log_query(query: str):
    if args.log is not None:
        args.log.write(query)
        args.log.write("\n")

def execute_with_timeout(f: Callable, passedLines, args) -> Any:
    p = mp.Process(target=f, args=[passedLines])
    start = time.monotonic()
    p.start()
    # Kill after `args.tlimit` seconds
    tlimit_s = args.tlimit / 1000
    p.join(tlimit_s)
    if p.is_alive():
        print(f"Timeout in model generation after {time.monotonic() - start:.2f} seconds!", file=sys.stderr)
        print("unknown", flush=True)
        p.kill()
        p.join()
        sys.exit(1)

def print_model(passedLines):
    # https://stackoverflow.com/questions/30134297/python-multiprocessing-stdin-input
    sys.stdin = open(0)
    m = get_model(passedLines)
    print(m, flush=True)

def run_z3(args, queryLines):
    z3.set_param('timeout', args.tlimit)
    z3.set_param("smt.random-seed", args.seed)
    z3.set_param("model", True)
    z3.set_param("model.completion", True)
    z3.Context.__del__ = lambda self: None
    z3.Solver.__del__ = lambda self: None
    execute_with_timeout(print_model, queryLines, args)
   
def get_query():
    log_query("% ---")
    # lines we've passed to Z3 thus far
    passedLines = []
    for line in sys.stdin:
        log_query(line)
        # Overwrite the behaviour of `(get-model)` to print the model in a more readable format
        if "(get-model)" in line:
            return passedLines
        # Execute all other commands as usual
        else:
            passedLines.append(line)
    raise Exception("No (get-model) was issued!")

if __name__ == '__main__':
    args = parser.parse_args()
    queryLines = get_query()    
    run_z3(args, queryLines)