module

public meta import Veil.Frontend.DSL.Module.Util.LocalRProp
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Core.Tools.Verifier.Manager
public meta import Veil.Frontend.DSL.Infra.Metadata
meta import Std.Sync.Mutex

public meta section

namespace Veil
open Lean Meta Elab Tactic

register_option veil.frame : Bool := {
  defValue := true
  descr := "Use structural frame proofs first for supported invariant preservation VCs."
}

/-- The frame rule handles guards and choices followed by one call to the postcondition. -/
private structure FrameAction where
  numGuards : Nat
  changedFields : NameSet

/-- Recognize both Lean encodings of a projection from the input state. -/
private def copiesField (env : Environment) (info : StructureInfo) (state : Expr) (field : Name) :
    Expr → Bool
  | .proj struct i obj => obj == state && struct == info.structName && info.fieldNames[i]? == some field
  | .app proj obj => obj == state && (getProjFnForField? env info.structName field).any proj.getAppFn.isConstOf
  | _ => false

/-- Open the extracted WP with fresh locals so references to the input state,
reader, and postcondition retain their identity under any number of guards. -/
private def inspectFrameAction (act stateName : Name) : MetaM FrameAction := do
  let wp ← getConstInfoDefn (toWpLocalPredName act)
  lambdaTelescope wp.value fun params body => do
    let state :: reader :: post :: _ := params.toList.reverse | throwError "expected WP parameters"
    forallTelescope body fun guards body => do
      let .app (.app (.app k _) rd) next := body | throwError "expected a postcondition call"
      unless k == post && rd == reader do throwError "unsupported frame WP"
      if next == state then return ⟨guards.size, {}⟩
      let env ← getEnv
      let some info := getStructureInfo? env stateName | throwError "expected a state structure"
      unless next.getAppFn.isConstOf (stateName ++ `mk) do throwError "expected a state constructor"
      let values := next.getBoundedAppArgs info.fieldNames.size
      unless values.size == info.fieldNames.size do throwError "expected a value for each state field"
      let mut changed := {}
      for field in info.fieldNames, value in values do
        unless copiesField env info state field value do
          changed := changed.insert field
      return ⟨guards.size, changed⟩

/-- The core takes theory fields followed by state fields in declaration order.
Pair those binders with their field names and look for uses of changed fields,
including uses as arguments to opaque functions. -/
private def checkFrameReads (mod : Module) (inv : Name) (changed : NameSet) : MetaM Unit := do
  if changed.isEmpty then return
  let inst ← getConstInfoDefn (inv ++ `instLocalRProp)
  lambdaTelescope inst.value fun _ value => do
    let .app (.app _ core) _ := value | throwError "expected a LocalRProp constructor"
    let fields := mod.immutableComponents ++ mod.mutableComponents
    lambdaBoundedTelescope core fields.size fun binders body => do
      unless binders.size == fields.size do throwError "expected one binder per field"
      let reads := (collectFVars {} body).fvarSet
      for field in fields, binder in binders do
        if changed.contains field.name && reads.contains binder.fvarId! then
          throwError "action updates field {field.name} used by the invariant"

/-- Follow the assembled conjunction to the requested clause, projecting its
proof from the pre-state hypothesis along the same path. -/
private def projectInvariant (pre post rd st : Expr) : MetaM Expr := do
  let preDef ← getConstInfoDefn pre.getAppFn.constName!
  let wanted := mkApp2 post rd st
  withLocalDeclD `h (mkApp2 pre rd st) fun h => do
    let mut proof := h
    let mut clause := preDef.value.beta (pre.getAppArgs ++ #[rd, st])
    while clause != wanted do
      let some (head, tail) := clause.and? | throwError "expected a clause of Invariants"
      if head == wanted then
        proof := .proj ``And 0 proof
        break
      clause := tail
      proof := .proj ``And 1 proof
    mkLambdaFVars #[rd, st, h] proof

/-- Construct the frame certificate directly out of previously checked
definitions. No simplifier, typeclass search, or proof search on the VC. -/
private def frameProof (mod : Module) (target : Expr) : MetaM Expr := do
  let_expr VeilM.meetsSpecificationIfSuccessfulAssuming _ ρ σ _ act assu pre post := target
    | throwError "expected an invariant preservation WP"
  let some actName := act.getAppFn.constName? | throwError "expected a named action"
  let some postName := post.getAppFn.constName? | throwError "expected a named invariant"
  let some preName := pre.getAppFn.constName? | throwError "expected pre-state invariants"
  let ns := preName.getPrefix
  unless preName == ns ++ assembledInvariantsName do
    throwError "expected the assembled pre-state invariants"
  let shape ← inspectFrameAction actName (ns ++ stateName)
  checkFrameReads mod postName shape.changedFields
  let postInst := mkAppN (mkConst (postName ++ `instLocalRProp)) post.getAppArgs
  let success := mkLambda `_ .default (mkConst ``Int) (mkConst ``True)
  let postFn := mkLambda `_ .default (mkConst ``Unit) post
  let hwp := mkAppN (mkConst (toWpLocalEqName actName)) (act.getAppArgs ++ #[success, postFn, postInst])
  withLocalDeclD `rd ρ fun rd => withLocalDeclD `st σ fun st => do
    let hwpType ← inferType (mkApp2 hwp rd st)
    let some (_, _, rhs) := hwpType.eq? | throwError "expected extracted WP equality"
    -- The abstract WP is applied to the handler, continuation, reader, and state.
    let pred := rhs.getBoundedAppFn 4
    let extract ← projectInvariant pre post rd st
    let bridge := mkAppN (mkConst (ns ++ frameTheoremName))
      (post.getAppArgs.take mod.parameters.size ++ #[act, assu, pre, post, postInst, pred, extract, hwp])
    let .forallE _ keepType _ _ ← inferType bridge | throwError "expected frame premise"
    let numFields := mod.immutableComponents.size + mod.mutableComponents.size
    let keep ← forallBoundedTelescope keepType (some numFields) fun fields premise =>
      forallBoundedTelescope premise (some 1) fun hyps wp => do
        let #[hpre] := hyps | throwError "expected the pre-state clause"
        forallBoundedTelescope wp (some shape.numGuards) fun guards _ =>
          mkLambdaFVars (fields ++ #[hpre] ++ guards) hpre
    return mkApp bridge keep

/-- Build a closed witness for an already elaborated VC. -/
def mkFrameProof (mod : Module) (goalType : Expr) : MetaM Expr := do
  let proof ← forallTelescope goalType fun params body => do
    mkLambdaFVars params (← frameProof mod body)
  let env ← getEnv
  let lctx ← getLCtx
  let .ok actual := Kernel.check env lctx proof | throwError "invalid frame certificate"
  unless actual == goalType || Kernel.isDefEqGuarded env lctx actual goalType do
    throwError "frame certificate has the wrong type"
  return proof

/-- The frame workers for one action share typed WP goals indexed by the exact
parameter binders of their public VCs. All analysis runs when a worker is tried. -/
structure FrameDischarger where
  private proc : ProcedureInfo
  private targets : Std.Mutex (Array (Array (TSyntax ``Parser.Term.bracketedBinder) × NameMap Expr))

def FrameDischarger.forAction (proc : ProcedureInfo) : BaseIO FrameDischarger := do
  return ⟨proc, ← Std.Mutex.new #[]⟩

/-- The action and every binder are shared by all of its clause VCs with the
same parameter telescope. Elaborate one such VC, then recover the other
clause applications directly from the assembled conjunction. -/
private def frameClauseTargets (sample : VCStatement) : TermElabM (NameMap Expr) := do
  forallTelescope (← sample.type) fun params target => do
    let_expr VeilM.meetsSpecificationIfSuccessfulAssuming _ _ _ _ _ _ pre _ := target
      | return {}
    let some preName := pre.getAppFn.constName? | return {}
    let conjunction := (← getConstInfoDefn preName).value.beta pre.getAppArgs
    lambdaBoundedTelescope conjunction 2 fun states body => do
      let mut remaining := body
      let mut targets := {}
      repeat
        let and? := remaining.and?
        let clause := (and?.map Prod.fst).getD remaining
        let post := clause.getBoundedAppFn 2
        if let some name := post.getAppFn.constName? then
          if clause == mkAppN post states then
            targets := targets.insert name (← mkForallFVars params (mkApp target.appFn! post))
        let some (_, tail) := and? | break
        remaining := tail
      return targets

/-- Elaborate the first WP in each binder order once. Workers for sibling clauses
use the same typed goals, even when they start concurrently. -/
private def FrameDischarger.clauseGoal? (self : FrameDischarger) (clause : Name) (vc : VCStatement) :
    TermElabM (Option Expr) :=
  self.targets.atomically fun cache => do
    if let some (_, targets) := (← cache.get).find? (fun (params, _) => params == vc.params) then
      return targets.find? clause
    let targets ← frameClauseTargets vc
    cache.modify (·.push (vc.params, targets))
    return targets.find? clause

/-- Try the frame rule on one invariant VC. Initializers and relational goals
decline before goal elaboration. A successful worker returns a kernel-checked proof. -/
def FrameDischarger.proveInvariant (self : FrameDischarger) (vc : VCData VCMetadata) : TermElabM Witness := do
  let .action act false := self.proc | throwError "expected an ordinary action"
  let .induction info := vc.metadata | throwError "expected an invariant VC"
  unless info.style == .wp && info.action == act do throwError "expected this action's WP"
  let clause := (← getCurrNamespace) ++ info.property
  let some target ← self.clauseGoal? clause vc.toVCStatement | throwError "expected a pre-state invariant clause"
  mkFrameProof (← getCurrentModule) target

/-- Close a raw invariant-preservation VC by returning its pre-state clause
under the action's guards when the clause's fields are unchanged. -/
elab "veil_frame" : tactic => liftMetaTactic fun goal => goal.withContext do
  goal.assign (← mkFrameProof (← getCurrentModule) (← goal.getType))
  return []

end Veil
