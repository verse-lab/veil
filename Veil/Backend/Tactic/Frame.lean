module

public meta import Veil.Frontend.DSL.Module.Util.LocalRProp
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Core.Tools.Verifier.Manager
public meta import Veil.Frontend.DSL.Infra.Metadata
meta import Std.Sync.Mutex

/-!
# Framing a weakest-precondition invariant goal

Suppose an action updates `live` and a clause of `Invariants` says `counter ≤ 2`.
The pre-state hypothesis already contains a proof of that clause. If the action
copies `counter` into the post-state, the same proof has the required post-state
type. The scoped tactic `veil_frame` and the frame worker for `#check_invariants`
both construct this proof on the raw weakest-precondition (WP) goal.

Two generated definitions tell us when to try this construction.

* The action's extracted WP must end in a single call `post result reader next`,
  possibly under binders for guards and nondeterministic choices. Inspecting
  `next` tells us which state fields the action copies from the input state.
* The clause's `LocalRProp.core` takes theory and state fields as arguments.
  Opening it with fresh locals tells us which named fields occur in the clause.
  If a field that occurs there is updated, framing declines. For example,
  `counter := 1` also preserves `counter ≤ 2`, but proving that needs a
  different argument.

For an eligible clause we supply the three premises of the module's frame
theorem (see `Module.defineFrameTheorem`):

* `extract` projects the requested clause out of the pre-state conjunction.
* `hwp` is the action's existing `wp_local_eq` theorem instantiated at this clause.
  It connects the public WP to the extracted predicate on individual field values.
* `keep` takes the field values, the pre-state clause proof, and the action's
  guards and choices. It returns the clause proof. Because the fields used by
  the clause are copied, its post-state type is definitionally equal.

Lean's kernel checks the assembled term against the original VC. Construction
uses neither a solver nor a simplifier. When the worker declines, the verifier
continues with the next discharger.
-/

public meta section

namespace Veil
open Lean Meta Elab Tactic

/-! ## Recognizing when the clause is unchanged -/

/-- What proof construction needs from the WP. Both guards and choices introduce
binders between the pre-state hypothesis and the postcondition. -/
private structure FrameAction where
  numWpBinders : Nat
  changedFields : NameSet

/-- A copy must project the *same named field* from the *input state*. Lean can
encode this either as a kernel projection (whose index we resolve using the
structure declaration) or as an application of the generated projection function. -/
private def copiesField (env : Environment) (info : StructureInfo) (state : Expr) (field : Name) :
    Expr → Bool
  | .proj struct i obj => obj == state && struct == info.structName && info.fieldNames[i]? == some field
  | .app proj obj => obj == state && (getProjFnForField? env info.structName field).any proj.getAppFn.isConstOf
  | _ => false

/-- Recover the possibly changed fields from the state passed to the continuation.
The extracted WP can pass the input state directly or construct a new record.
Constructor arguments end with one value per field in declaration order. -/
private def changedStateFields (stateName : Name) (state next : Expr) : MetaM NameSet := do
  if next == state then return {}
  let env ← getEnv
  let some info := getStructureInfo? env stateName | throwError "expected a state structure"
  unless next.getAppFn.isConstOf (stateName ++ `mk) do throwError "expected a state constructor"
  let values := next.getBoundedAppArgs info.fieldNames.size
  unless values.size == info.fieldNames.size do throwError "expected a value for each state field"
  let mut changed := {}
  for field in info.fieldNames, value in values do
    unless copiesField env info state field value do
      changed := changed.insert field
  return changed

/-- Recognize `fun … post reader state => ∀ guards/choices, post result reader next`.
Comparing fresh locals ensures that a binder introduced by a choice cannot be
mistaken for the original continuation, reader, or state. -/
private def inspectFrameAction (act stateName : Name) : MetaM FrameAction := do
  let wp ← getConstInfoDefn (toWpLocalPredName act)
  lambdaTelescope wp.value fun params body => do
    let state :: reader :: post :: _ := params.toList.reverse | throwError "expected WP parameters"
    forallTelescope body fun guards body => do
      let .app (.app (.app k _) rd) next := body | throwError "expected a postcondition call"
      unless k == post && rd == reader do throwError "unsupported frame WP"
      return ⟨guards.size, ← changedStateFields stateName state next⟩

/-- The core takes theory fields followed by state fields in declaration order.
Pair those binders with their field names and look for uses of changed fields,
including uses as arguments to opaque functions. -/
private def checkClauseFieldsUnchanged (mod : Module) (inv : Name) (changed : NameSet) : MetaM Unit := do
  if changed.isEmpty then return
  let inst ← getConstInfoDefn (inv ++ `instLocalRProp)
  lambdaTelescope inst.value fun _ value => do
    -- The generated instance ends in `LocalRProp.mk … core core_eq`.
    let .app (.app _ core) _ := value | throwError "expected a LocalRProp constructor"
    let fields := mod.immutableComponents ++ mod.mutableComponents
    lambdaBoundedTelescope core fields.size fun binders body => do
      unless binders.size == fields.size do throwError "expected one binder per field"
      let reads := (collectFVars {} body).fvarSet
      for field in fields, binder in binders do
        if changed.contains field.name && reads.contains binder.fvarId! then
          throwError "action updates field {field.name} used by the invariant"

/-! ## Supplying the three premises of the frame theorem -/

/-- Follow the assembled conjunction to the requested clause, projecting its
proof from the pre-state hypothesis along the same path. The last clause
is the tail itself, including when it is the only clause. -/
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

/-- Instantiate `wp_local_eq` for a successful execution returning `Unit`. Its
right-hand side has the form `pred handler continuation reader state`. Recovering
`pred` from that equality preserves the parameters chosen by WP extraction. -/
private def instantiateLocalWpEquality (actName : Name) (act post postInst rd st : Expr) :
    MetaM (Expr × Expr) := do
  let success := mkLambda `_ .default (mkConst ``Int) (mkConst ``True)
  let postFn := mkLambda `_ .default (mkConst ``Unit) post
  let hwp := mkAppN (mkConst (toWpLocalEqName actName)) (act.getAppArgs ++ #[success, postFn, postInst])
  let hwpType ← inferType (mkApp2 hwp rd st)
  let some (_, _, rhs) := hwpType.eq? | throwError "expected extracted WP equality"
  return (hwp, rhs.getBoundedAppFn 4)

/-- Construct `fun fields hpre guards => hpre` at the theorem's remaining premise.
Open exactly the WP binders counted by `inspectFrameAction`. A clause can itself
begin with `∀` or an implication, and those binders belong to the proof we return. -/
private def mkKeepProof (mod : Module) (shape : FrameAction) (keepType : Expr) : MetaM Expr := do
  let numFields := mod.immutableComponents.size + mod.mutableComponents.size
  forallBoundedTelescope keepType (some numFields) fun fields premise =>
    forallBoundedTelescope premise (some 1) fun hyps wp => do
      let #[hpre] := hyps | throwError "expected the pre-state clause"
      forallBoundedTelescope wp (some shape.numWpBinders) fun guards _ =>
        mkLambdaFVars (fields ++ #[hpre] ++ guards) hpre

/-- Match an open public VC, check the clause's fields, then apply the module
theorem with `extract`, `hwp`, and `keep` in declaration order. -/
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
  checkClauseFieldsUnchanged mod postName shape.changedFields
  let postInst := mkAppN (mkConst (postName ++ `instLocalRProp)) post.getAppArgs
  withLocalDeclD `rd ρ fun rd => withLocalDeclD `st σ fun st => do
    let extract ← projectInvariant pre post rd st
    let (hwp, pred) ← instantiateLocalWpEquality actName act post postInst rd st
    let moduleArgs := post.getAppArgs.take mod.parameters.size
    let bridge := mkAppN (mkConst (ns ++ frameTheoremName))
      (moduleArgs ++ #[act, assu, pre, post, postInst, pred, extract, hwp])
    let .forallE _ keepType _ _ ← inferType bridge | throwError "expected frame premise"
    return mkApp bridge (← mkKeepProof mod shape keepType)

/-- Common entry point for the tactic and worker. Rebind the VC parameters and
check the result against the full target before returning it to either caller. -/
def mkFrameProof (mod : Module) (goalType : Expr) : MetaM Expr := do
  let proof ← forallTelescope goalType fun params body => do
    mkLambdaFVars params (← frameProof mod body)
  let env ← getEnv
  let lctx ← getLCtx
  let .ok actual := Kernel.check env lctx proof | throwError "invalid frame certificate"
  unless actual == goalType || Kernel.isDefEqGuarded env lctx actual goalType do
    throwError "frame certificate has the wrong type"
  return proof

/-! ## Adapting the proof builder to verifier workers and interactive tactics -/

/-- Per-action cache of elaborated targets. Two public VCs can quantify their
`Decidable` instances in different orders, so the key includes the exact binder
syntax. Only closed targets are shared between workers. -/
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
          -- Only a named clause applied to this reader and state is a sibling VC.
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
scoped elab "veil_frame" : tactic => liftMetaTactic fun goal => goal.withContext do
  goal.assign (← mkFrameProof (← getCurrentModule) (← goal.getType))
  return []

end Veil
