import LeanSts.State
import Auto

set_option trace.auto.lamReif.prep.printResult true
set_option trace.auto.lamReif.printResult true

set_option trace.auto.mono true
set_option trace.auto.mono.match true
set_option trace.auto.mono.printConstInst true
set_option trace.auto.mono.printLemmaInst true
set_option trace.auto.mono.printResult true

set_option trace.auto.collectInd true
set_option trace.auto.lamFOL2SMT true

set_option auto.smt true
set_option auto.smt.trust true
set_option trace.auto.printLemmas true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

section SMT
structure TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

/-

Want to generate something like the following. Note that we are NOT
generating a datatype, but rather an _instance_ of a datatype.
The overall process I envision is to collect all instances of the structure
in the context (when `auto` or an equivalent tactic is invoked) and generate
an instance of `le` (and the axioms) for each, e.g. `le_1`, `le_2`, etc.
This corresponds to what Ivy does when it unfolds the transition relation,
possibly multiple times.

(declare-sort t)
(declare-fun le (t t) Bool)
(assert (forall ((x t)) (le x x)))
(assert (forall ((x t) (y t) (z t)) (=> (and (le x y) (le y z)) (le x z))))
(assert (forall ((x t) (y t)) (=> (and (le x y) (le y x)) (= x y))))
(assert (forall ((x t) (y t)) (or (le x y) (le y x)))

(check-sat)
-/

example : ∃ (t : TotalOrder Nat), True := by
  auto

open Lean Elab Tactic Meta
syntax (name := gen_smt) "gen_smt" term : tactic

set_option trace.gen_smt true
-- set_option trace.Elab.definition true

/-- Can this inductive type be translated to SMT? -/
def isSupportedInductiveType (indVal : InductiveVal) : Bool :=
  indVal.numIndices = 0 &&
  !indVal.isRec &&
  !indVal.isUnsafe &&
  !indVal.isNested &&
  -- not mutually inductive
  indVal.all.length = 1 &&
  -- TODO: relax this assumption
  -- is a structure / has only one constructor
  indVal.ctors.length = 1


def isNotSupportedBecause (indVal : InductiveVal) : Option String :=
  if indVal.numIndices ≠ 0 then
    some "inductive type has indices"
  else if indVal.isRec then
    some "inductive type is recursive"
  else if indVal.isUnsafe then
    some "inductive type is unsafe"
  else if indVal.isNested then
    some "inductive type is nested"
  else if indVal.all.length ≠ 1 then
    some "inductive type has more than one constructor"
  else
    none

-- https://github.com/opencompl/lean-mlir-semantics/blob/master/MLIRSemantics/Util/Metagen.lean#L110-L157
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Metaprogramming.20a.20structure.20declaration/near/369262671


set_option pp.all true
set_option pp.raw true

-- TODO: transform TotalOrder (after monomorphization) into a function and some axioms

@[tactic gen_smt]
def evalGenSMT : Tactic
| `(gen_smt | gen_smt $term) => withMainContext do
  let env ← getEnv
  let expr ← elabTerm term none false
  let typeName := expr.getAppFn.constName!
  let indVal ← getConstInfoInduct typeName
  if !(isSupportedInductiveType indVal) then
    let reason := isNotSupportedBecause indVal
    throwError "unsupported inductive type '{typeName}' because {reason.getD "unknown reason"}"
  -- at this point, guaranteed to have exactly one constructor and
  -- to have no funny business going on
  -- TODO: handle raw `inductive`s (not `structure`s) -- see `Structure.lean : isStructureLike`
  -- TODO: handle `structure`s with `extends`
  let some info := getStructureInfo? env typeName
   | throwError "{typeName} is not a structure"
  trace[gen_smt] "structure {info.structName} has fields {info.fieldNames}"
  for field in info.fieldInfo do
    if field.subobject?.isSome then
      continue
    let proj := (env.find? field.projFn).get!
    let projType := proj.type
    let isAxiom := (← isProp projType)
    -- TODO: distinguish between constants / relations / functions
    let typeStr := if isAxiom then "[axiom]" else "[function]"
    trace[gen_smt] "{typeStr} {field.fieldName} : {projType}"
| _ => throwUnsupportedSyntax

-- Problems with `lean-auto`:
-- (1) (in collectAppInstSimpleInduct) Warning: TotalOrder or some type within the same mutual block is not a simple inductive type.
-- (2) (in lamSort2SSort) Only first-order types are translated

example : True := by
  gen_smt (TotalOrder (Fin 5))
  exact True.intro
end SMT
