module

public meta import Veil.Frontend.DSL.Module.VCGen.Common
public meta import Veil.Backend.SMT.Model
public meta import Veil.Core.Tools.Synthesizer.Tactic
public meta import Veil.Frontend.DSL.Tactic.Core

public meta section

open Lean Meta Elab Term

namespace Veil

private def checkClosed (e : Expr) : MetaM Unit := do
  if e.hasFVar || e.hasMVar || e.hasSorry then throwError "open or admitted witness"
  checkWithKernel e
  for n in e.getUsedConstants do
    unless (← collectAxioms n).all Synthesizer.standardAxioms.contains do
      throwError "nonstandard axiom in witness"

/-- Check the arguments even for unused binders, which disappear after substitution. -/
def specializeWitness (template : Expr) (args : Array Expr) : MetaM Expr := do
  let mut result := template
  for arg in args do
    let .forallE _ domain body _ ← whnf result | throwError "unexpected witness argument"
    checkClosed (← mkExpectedTypeHint arg domain)
    result := body.instantiate1 arg
  return result

/-- Specialize the original telescope to the decoded module and canonical state representation. -/
def specializeWitnessModule (template : Expr) (params : Array Parameter) (theoryType stateType : Expr)
    (enums : Array EnumSortAdaptation) : TermElabM Expr := do
  let mut result := template
  let mut i := 0
  for p in params do
    let .forallE _ domain body _ ← whnf result | throwError "missing module binder {p.name}"
    let arg ← match p.kind with
      | .sort _ | .userParameter => do
        let some arg := theoryType.getAppArgs[i]? | throwError "missing module argument {p.name}"
        i := i + 1
        pure arg
      | .backgroundTheory => pure theoryType
      | .environmentState => pure stateType
      | .fieldConcreteType => pure stateType.appArg!
      | .moduleTypeclass .userDefined => do
        -- The enum decoder supplies the interpretation of each constructor.
        -- Other user dictionaries are not part of the structural instantiation.
        let mod ← getCurrentModule
        let some (sp, _) := mod.sortParams.find? (fun (sp, k) =>
          k == .enumSort && Name.toEnumInst sp.name == p.name)
          | throwError "missing reconstructed instance {p.name}"
        let some e := enums.find? (fun e => e.enumType.isConstOf (mod.name ++ Name.toEnumConcreteTypeName sp.name))
          | throwError "missing constructor assignments for {sp.name}"
        let inst ← synthInstance domain
        for (_, ctor) in e.indexToCtor do
          let field := ctor.constName!.updatePrefix .anonymous
          unless ← isDefEq (← mkProjection inst field) ctor do throwError "enum assignment mismatch"
        pure inst
      | _ => forallTelescopeReducing domain fun xs target => do
        mkLambdaFVars xs (← synthInstance target)
    checkClosed (← mkExpectedTypeHint arg domain)
    result := body.instantiate1 arg
  return result

inductive WitnessCheck where
  | checked
  | invalid
  | unverified (reason : String := "")
deriving BEq, Repr

instance : ToJson WitnessCheck where
  toJson result := Id.run do
    let (status, message) := match result with
      | .checked => ("checked", "Lean checked the reconstructed states and actions")
      | .invalid => ("invalid", "Invalid reconstruction: the states or actions contradict the query")
      | .unverified reason => ("unverified", "Lean could not verify the reconstructed states and actions" ++
          (if reason.isEmpty then "" else s!" ({reason})"))
    return Json.mkObj [("status", toJson status), ("message", toJson message)]

/-- Prove the closed proposition (or its negation) independently of SMT. Discard
temporary tactic declarations and diagnostics after auditing the kernel-checked proof. -/
def checkWitness (obligation : TermElabM Expr) : TermElabM WitnessCheck := withCurrHeartbeats do
  -- Give replay its own bounded budget even when the SMT command runs without a limit.
  withTheReader Core.Context (fun c => { c with maxHeartbeats :=
    if c.maxHeartbeats == 0 then 20_000_000 else min c.maxHeartbeats 20_000_000 }) do
  let saved ← Term.saveState
  try
    tryCatchRuntimeEx (do
      let goal ← withoutErrToSorry obligation
      if goal.hasFVar || goal.hasMVar || goal.hasSorry then return .unverified
      let proves (p : Expr) : TermElabM Bool := do
        try
          let tactic ← `(by veil_concrete [$(mkIdent `nextSimp):ident, $(mkIdent `invSimp):ident])
          let proof ← withoutErrToSorry <| elabTermAndSynthesize tactic (some p)
          checkClosed (mkExpectedPropHint proof p)
          return true
        catch _ => return false
      if ← proves goal then return .checked
      if ← proves (mkNot goal) then return .invalid
      return .unverified) fun ex => do
        if ex.isRuntime then return .unverified "replay resource limit reached"
        let reason := (← ex.toMessageData.toString).splitOn "\n" |>.head!
        return .unverified (reason.take 180).toString
  finally saved.restore (restoreInfo := true)

end Veil
