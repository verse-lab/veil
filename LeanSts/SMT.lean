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

example : ∃ (t : TotalOrder (Fin 5)), True := by
  auto

open Lean Elab Tactic
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
  -- TODO: handle raw `inductive`s (not `structure`s)
  -- TODO: handle `structure`s with `extends`
  let some info := getStructureInfo? env typeName
   | throwError "{typeName} is not a structure"
  trace[gen_smt] "structure {info.structName} has fields {info.fieldNames}"
  for field in info.fieldInfo do
    let proj := (env.find? field.projFn).get!
    let projType := proj.type
    trace[gen_smt] "field {field.fieldName} has type {projType}"
| _ => throwUnsupportedSyntax

-- TODO: transform TotalOrder (after monomorphization) into a function and some axioms

example : True := by
  gen_smt (TotalOrder (Fin 5))
  exact True.intro
end SMT
