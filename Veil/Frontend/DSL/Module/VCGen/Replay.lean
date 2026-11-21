module

public meta import Veil.Frontend.DSL.Module.VCGen.Common
public meta import Veil.Core.UI.Verifier.InductionCounterexample
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

def checkWitnessArg (arg domain : Expr) : MetaM Unit := do
  checkClosed (← mkExpectedTypeHint arg domain)

/-- Check the arguments even for unused binders, which disappear after substitution. -/
def specializeWitness (template : Expr) (args : Array Expr) : MetaM Expr := do
  let mut result := template
  for arg in args do
    let .forallE _ domain body _ ← whnf result | throwError "unexpected witness argument"
    checkWitnessArg arg domain
    result := body.instantiate1 arg
  return result

/-- Preserve the model context's binder identities, including projected fields. -/
def witnessAssignments (ctx : Smt.ModelContext) (extras : Array (Expr × Expr)) :
    TermElabM (Std.HashMap Name Expr) := do
  let mut values := {}
  for (key, value) in extras do
    let some name ← getExprName ctx key | throwError "unnamed model assignment"
    if values.contains name then throwError "ambiguous model assignment {name}"
    values := values.insert name value
  return values

/-- Elaborate the same structure literal and law proofs as the UPDR certifier.
SMT already supplies Lean expressions for the data fields. Adapt each at the
type Lean expects, after the preceding fields have been instantiated. -/
private def rebuildInstance (domain : Expr) (name : Name) (values : Std.HashMap Name Expr)
    (enums : Array EnumSortAdaptation) : TermElabM Expr := do
  if values.contains (modelInstanceName name) then
    return ← buildModelValue values (modelInstanceName name) domain enums
  let some cls := (← whnf domain).getAppFn.constName? | throwError "unsupported instance {name}"
  let some info := getStructureInfo? (← getEnv) cls
    | throwError "unsupported instance {name}"
  let rec go (fields : List Name) (terms : Array (Name × Term)) : TermElabM Expr := do
    match fields with
    | [] => elabTermAndSynthesize (← Synthesizer.structInstance terms) (some domain)
    | field :: rest =>
      elabToSyntax (fun expected => do
        let some ty := expected | throwError "missing field type for {name}.{field}"
        let ty ← instantiateMVars ty
        if ← isProp ty then elabTermAndSynthesize (← Synthesizer.modelLaw) (some ty)
        else buildModelValue values (modelInstanceName (name ++ field)) ty enums)
        fun t => go rest (terms.push (field, t))
  go info.fieldNames.toList #[]

/-- Specialize the original telescope to the decoded module and canonical state representation. -/
def specializeWitnessModule (template : Expr) (params : Array Parameter) (theoryType stateType : Expr)
    (enums : Array EnumSortAdaptation) (values : Std.HashMap Name Expr) : TermElabM Expr := do
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
        let mod ← getCurrentModule
        let some (sp, _) := mod.sortParams.find? (fun (sp, k) =>
          k == .enumSort && Name.toEnumInst sp.name == p.name)
          | rebuildInstance domain p.name values enums
        let some e := enums.find? (fun e => e.enumType.isConstOf (mod.name ++ Name.toEnumConcreteTypeName sp.name))
          | throwError "missing constructor assignments for {sp.name}"
        let inst ← synthInstance domain
        for (idx, ctor) in e.indexToCtor do
          let field := ctor.constName!.updatePrefix .anonymous
          let some raw := values[modelInstanceName (p.name ++ field)]?
            | throwError "missing constructor assignment for {field}"
          let index ← mkAppOptM ``OfNat.ofNat #[some e.smtType, some (mkNatLit idx), none]
          checkWitnessArg raw e.smtType
          unless (← isDefEq raw index) && (← isDefEq (← mkProjection inst field) ctor) do
            throwError "enum assignment mismatch"
        pure inst
      | _ => forallTelescopeReducing domain fun xs target => do
        mkLambdaFVars xs (← synthInstance target)
    checkWitnessArg arg domain
    result := body.instantiate1 arg
  return result

/-- Instantiate universally quantified picks and invariant counter-witnesses on the
implication spine. The proof we construct goes from the original WP to this particular
instance. Refuting the instance therefore refutes the WP. -/
partial def checkWPChoices (original : Expr) (actName : Name) (choices : Std.HashMap Name Expr)
    (enums : Array EnumSortAdaptation) : TermElabM Expr := do
  let reduced ← Veil.Simp.simp #[toWpEqName actName, toWpName actName, `invSimp, `derivedInvSimp] {} original
  let rec pin (h ty : Expr) (pending : Std.HashMap Name Expr) : TermElabM Expr := do
    let .forallE n domain body info ← whnf ty | do
      if let some (n, _) := pending.toList.head? then throwError "unmatched WP assignment {n}"
      return h
    if choices.contains n && !(← isProp domain) then
      unless pending.contains n do throwError "ambiguous WP binder {n}"
      let value ← buildModelValue choices n domain enums
      -- SMT models Nat as Int. A negative integer has no corresponding Lean pick.
      let raw := choices[n]!
      if (← whnf domain).isNat && (← whnf (← inferType raw)).isInt then
        unless ← isDefEq (← mkAppM ``Int.ofNat #[value]) raw do throwError "invalid Nat assignment {n}"
      checkWitnessArg value domain
      return ← pin (mkApp h value) (body.instantiate1 value) (pending.erase n)
    withLocalDecl n info domain fun x => do
      mkLambdaFVars #[x] (← pin (mkApp h x) (body.instantiate1 x) pending)
  let implication ← withLocalDeclD `h original fun h => do
    let proof ← if let some eq := reduced.proof? then mkEqMP eq h else pure h
    mkLambdaFVars #[h] (← pin proof reduced.expr choices)
  checkClosed implication
  let .forallE _ _ result _ ← inferType implication | throwError "unexpected WP specialization"
  return mkNot result

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
