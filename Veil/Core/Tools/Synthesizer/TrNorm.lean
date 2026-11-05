module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Query

/-!
# The normalized transition relation

Veil's preprocessing of a query unfolds each action's semantics into a proposition over the fields
of the two states, the same in every query. This file does that once per module: it adds the
definition `Mod.ic3_trNorm`, whose body is that proposition for each action, and the theorem
`Mod.ic3_tr_eq_norm` that it equals Veil's `tr`, checked by the kernel. Queries are then written
with `ic3_trNorm`, and certificates rewrite along the equation.

## Main definitions

* `Veil.Synthesizer.TrNorm.ensure`: add the two declarations once, and return the definition.
* `Veil.Synthesizer.QueryCtx.normalizedTr?`: the relation to write a query's transitions with.
* `Veil.Synthesizer.addCheckedDecl`: add a declaration only if the kernel accepts it.

## Implementation notes

* The two names are reserved: a declaration under them that this process did not build and the
  kernel did not check is an error, never used in its place (`TrNorm.throwIfForeign`).
* A failed normalization restores the environment, warns once, and leaves the module's queries
  written with `tr`.
* With `set_option veil.synthesizer.normalizeTr false` every query is written with `tr`.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Term Meta Veil

register_option veil.synthesizer.normalizeTr : Bool := {
  defValue := true
  descr := "write the queries with the normalized transition relation `Mod.ic3_trNorm`, built \
    once per module, instead of Veil's `tr`"
}

register_option veil.synthesizer.debug.failNormalize : String := {
  defValue := ""
  descr := "make the normalization of the transition relation fail \"before\" anything is built \
    or \"afterDef\", after the definition and before the equation, to exercise the fallback to \
    Veil's `tr` (for tests)"
}

/-- Add a declaration the kernel accepts, and nothing otherwise. Lean's `addDecl` registers a
rejected declaration as an axiom, so the kernel first checks it in a dry run. -/
def addCheckedDecl (d : Declaration) : CoreM Unit :=
  withOptions (fun o ↦ maxHeartbeats.set (Elab.async.set o false) 0) do
    match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) d with
    | .error ex => throwKernelException ex
    | .ok _ => withOptions (debug.skipKernelTC.set · true) (addDecl d)

namespace TrNorm

/-- `Mod.ic3_trNorm`, the normalized transition relation. -/
def defName (mod : Veil.Module) : Name := mod.name ++ `ic3_trNorm

/-- `Mod.ic3_tr_eq_norm : ∀ …, tr th st0 lbl st1 = ic3_trNorm … th st0 lbl st1`. -/
def eqName (mod : Veil.Module) : Name := mod.name ++ `ic3_tr_eq_norm

/-- The declarations this process built for a module, as the kernel checked them. -/
structure Record where
  mod : Name
  defType : Expr
  defValue : Expr
  eqType : Expr
  eqValue : Expr

/-- Whether the environment holds the declarations of `r` under their names. -/
def Record.holdsIn (r : Record) (env : Environment) : Bool :=
  match env.find? (r.mod ++ `ic3_trNorm), env.find? (r.mod ++ `ic3_tr_eq_norm) with
  | some (.defnInfo d), some (.thmInfo t) =>
    d.type == r.defType && d.value == r.defValue && t.type == r.eqType && t.value == r.eqValue
  | _, _ => false

/-- The normalized transition relations this process built. -/
initialize built : IO.Ref (Array Record) ← IO.mkRef #[]

/-- The modules whose normalization failed in this process; they are not tried again. -/
initialize failed : IO.Ref (Array Name) ← IO.mkRef #[]

/-- The record of `mod`, if this process built its normalized transition relation. -/
def record? (mod : Veil.Module) : IO (Option Record) := do
  return (← built.get).find? (·.mod == mod.name)

/-- The normalized transition relation of `mod`, when the option is on and the environment holds
the declarations this process built. -/
def available (mod : Veil.Module) : CoreM (Option Name) := do
  unless veil.synthesizer.normalizeTr.get (← getOptions) do return none
  let some r ← record? mod | return none
  return if r.holdsIn (← getEnv) then some (defName mod) else none

/-- Fail when a reserved name is declared and does not hold what this process built. -/
def throwIfForeign (mod : Veil.Module) : CoreM Unit := do
  unless veil.synthesizer.normalizeTr.get (← getOptions) do return
  let env ← getEnv
  if (← record? mod).any (·.holdsIn env) then return
  for n in [defName mod, eqName mod] do
    if env.contains n then
      throwError "IC3: {n} is already declared; the names `ic3_trNorm` and `ic3_tr_eq_norm` are \
        reserved for the normalized transition relation the command builds"

/-- The fault point `veil.synthesizer.debug.failNormalize` names. -/
def faultPoint : CoreM (Option String) := do
  match veil.synthesizer.debug.failNormalize.get (← getOptions) with
  | "" => return none
  | "before" => return some "before"
  | "afterDef" => return some "afterDef"
  | v => throwError "IC3: veil.synthesizer.debug.failNormalize is \"{v}\"; its values are \
      \"before\" and \"afterDef\""

/-- The simp context and simprocs of a `simp only […]` tactic, as the tactic elaborates them. -/
def simpContextOf (tac : TSyntax `tactic) : TermElabM (Simp.Context × Simp.SimprocsArray) := do
  let g ← mkFreshExprMVar (mkConst ``True)
  let x : Tactic.TacticM (Simp.Context × Simp.SimprocsArray) := do
    let r ← Tactic.mkSimpContext tac (eraseLocal := false)
    pure (r.ctx, r.simprocs)
  x.run { elaborator := .anonymous } |>.run' { goals := [g.mvarId!] }

/-- Build and add the two declarations. The definition is
`fun sorts [insts] th st0 lbl st1 ↦ Label.casesOn lbl P₁ … Pₙ`, where `Pₐ` is
`tr th st0 (Label.a args) st1` after the three `simp` passes of Veil's preprocessing; the theorem
is proven by cases on the label from the proofs of those passes. -/
def build (ctx : QueryCtx) (faultAt : Option String) : TermElabM Record := do
  let (st0, st1, lbl) := (stateIdent 0, stateIdent 1, mkIdent `lbl)
  let labelT ← `($(mkIdent labelTypeName) $(ctx.sorts)*)
  let binders ← (ctx.sortBinders ++ ctx.typeclassBinders).mapM bracketedBinderToFunBinder
  let fnStx ← `(fun $binders* ($(ctx.th) : $(ctx.theoryT)) ($st0 : $(ctx.stateT)) ($lbl : $labelT)
      ($st1 : $(ctx.stateT)) ↦ (($(ctx.rtsExpr)).$(mkIdent `tr) $(ctx.th) $st0 $lbl $st1 : Prop))
  let fn ← Term.withoutErrToSorry do
    let fn ← elabTerm fnStx none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars fn
  if fn.hasSorry || fn.hasMVar || fn.hasLevelMVar then
    throwError "IC3: the transition relation of {ctx.mod.name} did not elaborate"
  let fnTy ← instantiateMVars (← inferType fn)
  let passes ← [← `(tactic| simp only [$(mkIdent `nextSimp):ident]),
    ← `(tactic| simp only [↓ $(mkIdent ``Veil.existsQuantifierSimpGuarded):ident]),
    ← `(tactic| simp only [$(mkIdent `smtSimp):ident])].mapM simpContextOf
  let normalize (e : Expr) : TermElabM Simp.Result := do
    let mut r : Simp.Result := { expr := e }
    for (c, p) in passes do
      let (r', _) ← Meta.simp r.expr c p
      r ← r.mkEqTrans r'
    return r
  -- The definition, by cases on the label; each case's proof is kept for the theorem.
  let defMVar ← mkFreshExprMVar fnTy
  let (xs, g) ← defMVar.mvarId!.intros
  let lblVar := xs[xs.size - 2]!
  let body := (mkAppN fn (xs.map mkFVar)).headBeta
  let mut proofs : Array (Name × Expr) := #[]
  for sg in ← g.cases lblVar do
    let pf ← sg.mvarId.withContext do
      let r ← normalize (sg.subst.apply body)
      sg.mvarId.assign r.expr
      let args := ((xs.filter (· != lblVar)).map (sg.subst.apply <| mkFVar ·)) ++ sg.fields
      mkLambdaFVars args (← r.getProof)
    proofs := proofs.push (sg.ctorName.getD .anonymous, pf)
  let defValue ← instantiateMVars defMVar
  let name := defName ctx.mod
  addCheckedDecl (.defnDecl ⟨⟨name, [], fnTy⟩, defValue, .abbrev, .safe, [name]⟩)
  if faultAt == some "afterDef" then
    throwError "injected failure, veil.synthesizer.debug.failNormalize afterDef"
  -- The theorem, by cases on the label; the kernel checks each case by unfolding.
  let eqType ← instantiateMVars (← forallTelescope fnTy fun ys _ ↦ do
    mkForallFVars ys (← mkEq (mkAppN fn ys).headBeta (mkAppN (mkConst name) ys)))
  let eqMVar ← mkFreshExprMVar eqType
  let (ys, g) ← eqMVar.mvarId!.intros
  let lblY := ys[ys.size - 2]!
  for sg in ← g.cases lblY do
    let some (_, pf) := proofs.find? (·.1 == sg.ctorName.getD .anonymous)
      | throwError "IC3: no normalized transition for constructor {sg.ctorName}"
    let args := (ys.filter (· != lblY)).map (sg.subst.apply <| mkFVar ·)
    sg.mvarId.assign (pf.beta (args ++ sg.fields))
  let eqValue ← instantiateMVars eqMVar
  addCheckedDecl (.thmDecl ⟨⟨eqName ctx.mod, [], eqType⟩, eqValue, [eqName ctx.mod]⟩)
  return { mod := ctx.mod.name, defType := fnTy, defValue, eqType, eqValue }

/-- The normalized transition relation of the module, built on first use; `none` when the option
is off or the normalization failed, which restores the environment and warns once. -/
def ensure (ctx : QueryCtx) : TermElabM (Option Name) := do
  unless veil.synthesizer.normalizeTr.get (← getOptions) do return none
  if let some name ← available ctx.mod then return some name
  if (← failed.get).contains ctx.mod.name then return none
  throwIfForeign ctx.mod
  let faultAt ← faultPoint
  let t0 ← IO.monoMsNow
  let envBefore ← getEnv
  let r ← tryCatchRuntimeEx
    (do
      if faultAt == some "before" then
        throwError "injected failure, veil.synthesizer.debug.failNormalize before"
      let r ← build ctx faultAt
      built.modify fun rs ↦ (rs.filter (·.mod != ctx.mod.name)).push r
      pure (some (defName ctx.mod)))
    fun e ↦ do
      setEnv envBefore
      failed.modify (·.push ctx.mod.name)
      logWarning m!"IC3: the transition relation of {ctx.mod.name} could not be normalized \
        ({e.toMessageData}); its queries are written with Veil's `tr` and pay its preprocessing \
        on every call"
      return none
  notePhase (fun p dt ↦ { p with normalizeMs := p.normalizeMs + dt }) t0
  return r

/-- How a run stood to the normalized transition relation. -/
inductive Status where
  /-- Built during the run. -/
  | normalized
  /-- Built by an earlier run in the same module. -/
  | reused
  /-- The normalization failed. -/
  | failed
  /-- Turned off by `veil.synthesizer.normalizeTr`. -/
  | off
  /-- Not needed: the run asked no question about a transition. -/
  | unused
deriving BEq, Repr

/-- The status as the `trNorm` field of the log's `outcome` event. -/
def Status.key : Status → String
  | .normalized => "normalized"
  | .reused => "reused"
  | .failed => "failed"
  | .off => "off"
  | .unused => "unused"

/-- The status of `mod` after a run; `builtBefore` says whether it was available before. -/
def status (mod : Veil.Module) (builtBefore : Bool) : CoreM Status := do
  unless veil.synthesizer.normalizeTr.get (← getOptions) do return .off
  if (← failed.get).contains mod.name then return .failed
  if (← record? mod).isSome then return if builtBefore then .reused else .normalized
  return .unused

end TrNorm

/-- The relation to write the transitions of a query with: the normalized transition relation
when the module has actions and one can be built, Veil's `tr` (`none`) otherwise. -/
def QueryCtx.normalizedTr? (ctx : QueryCtx) : TermElabM (Option Name) :=
  if ctx.mod.actions.isEmpty then pure none else TrNorm.ensure ctx

end Veil.Synthesizer
