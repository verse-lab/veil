module

public meta import Veil
public meta import Veil.Core.Tools.ModelChecker.Symbolic.TraceLang
public meta import Veil.Core.UI.Verifier.TraceCounterexample
public meta import Veil.Frontend.DSL.Module.VCGen.Common
public meta import Veil.Core.Tools.Synthesizer.TrNorm

/-!
# Discharging queries

This file discharges the statement of a query (`QueryCtx.statement`) with Veil's own pipeline:
the preprocessing of `veil_bmc`, then lean-smt and cvc5.

## Main definitions

* `Veil.Synthesizer.QueryResult`: what a query returned.
* `Veil.Synthesizer.runStatement`: discharge a statement, with the unsat core of its trailing
  diagram literals on request.

## Implementation notes

* `unsat` comes with lean-smt's reconstructed proof of the statement, which contains `sorry` when
  the solver was trusted; `sat` comes with a model rendered by Veil's trace decoder.
* Unsat cores exist only on lean-smt's reconstruction path, so a query that asks for one is not
  trusted. When such a query's answer cannot be read, it is asked again without the core.
* A proof that lean-smt cannot replay is asked again trusting the solver: the verdict stands, and
  certificates reconstruct their own proofs.
* Each query runs under its own heartbeat budget; an overrun is `unknown`.
* `veil.synthesizer.trust` is separate from Veil's `veil.smt.trust`, so a module's setting of the
  latter does not weaken the synthesizer.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Command Term Meta Veil Lean.Parser.Term

register_option veil.synthesizer.trust : Bool := {
  defValue := false
  descr := "let the IC3 search take the solver's unsat answers on faith instead of reconstructing \
    proofs (certificates always reconstruct)"
}

register_option veil.synthesizer.debug.failQuery : String := {
  defValue := ""
  descr := "make every query over k transitions fail, for tests: \"unknown:k\" answers unknown \
    without asking the solver, \"undecoded:k\" takes a sat answer's model as one that did not \
    decode, \"throw:k\" throws once the statement is elaborated"
}

/-- What a query returned. -/
inductive QueryResult where
  /-- The conjunction is unsatisfiable: `proof` proves `statement`, with `sorry` when `viaTrust`. -/
  | unsat (statement : Expr) (proof : Expr) (viaTrust : Bool)
  /-- The conjunction is satisfiable, with `VeilTrace.toJson` of a model, or `null` when none was
  asked for. -/
  | sat (model : Json)
  /-- The conjunction is satisfiable, but the model asked for could not be read. -/
  | satUndecoded (reason : String)
  /-- The solver gave up, or the query overran its budget. -/
  | unknown (reason : String)
  /-- The question could not be posed or its answer could not be read. -/
  | error (message : String)

instance : ToString QueryResult := ⟨fun
  | .unsat _ _ viaTrust => s!"unsat{if viaTrust then " (solver trusted)" else ""}"
  | .sat _ => "sat"
  | .satUndecoded r => s!"sat, but the model could not be decoded: {r}"
  | .unknown r => s!"unknown: {r}"
  | .error m => s!"error: {m}"⟩

/-- The prefix of an `unknown` reason that the solver itself gave. -/
def solverUnknownPrefix : String := "solver returned unknown"

namespace QueryResult

/-- Whether the answer is an `unknown` the solver itself gave, which a larger timeout may change. -/
def solverGaveUp : QueryResult → Bool
  | .unknown r => r.startsWith solverUnknownPrefix
  | _ => false

/-- Whether the answer is an `unsat` taken on the solver's word. -/
def isTrusted : QueryResult → Bool
  | .unsat _ _ t => t
  | _ => false

end QueryResult

/-- The failure and transition count `veil.synthesizer.debug.failQuery` names. -/
def failQueryAt : CoreM (Option (String × Nat)) := do
  let v := veil.synthesizer.debug.failQuery.get (← getOptions)
  if v.isEmpty then return none
  if let [kind, k] := v.splitOn ":" then
    if let some n := k.toNat? then
      if ["unknown", "undecoded", "throw"].contains kind then return some (kind, n)
  throwError "IC3: veil.synthesizer.debug.failQuery is \"{v}\"; its values are \"unknown:k\", \
    \"undecoded:k\" and \"throw:k\" for a number of transitions k"

/-- The message of a failure injected by `veil.synthesizer.debug.failQuery`. -/
def injectedQueryFailure (kind : String) (k : Nat) : String :=
  s!"injected failure, veil.synthesizer.debug.failQuery {kind}:{k}"

/-! ### Tactics -/

/-- Veil's `veil_bmc` preprocessing, without the solver call. A normalized transition relation
`trNorm` is unfolded after the first two `simp` passes. -/
def preprocessTactic (trNorm : Option Name) (trust : Bool) : TermElabM (TSyntax `tactic) := do
  let inferNonempty ← if trust then `(tactic| skip) else `(tactic| veil_infer_nonempty)
  let unfoldNorm ← match trNorm with
    | some n => `(tactic| try dsimp only [$(mkIdent n):ident])
    | none => `(tactic| skip)
  let dsimpLemmas := #[mkIdent ``Inhabited.default, fieldAbstractDispatcher,
    fieldLabelToDomain stateName, fieldLabelToCodomain stateName]
  let dsimpTac ← `(tactic| try dsimp +$(mkIdent `instances) [$[$dsimpLemmas:ident],*])
  let inst := mkIdent `instances
  `(tactic| (
    $inferNonempty:tactic;
    veil_simp +$inst only [$(mkIdent `nextSimp):ident];
    veil_simp +$inst only [↓ $(mkIdent ``Veil.existsQuantifierSimpGuarded):ident];
    $unfoldNorm:tactic;
    veil_intros;
    $inferNonempty:tactic;
    veil_destruct;
    $dsimpTac:tactic;
    veil_simp +$inst only [$(mkIdent `smtSimp):ident];
    $dsimpTac:tactic))

/-- The `smt` call Veil's `veil_smt` makes, with the hypotheses `hyps`. -/
def smtTactic (hyps : Array Ident) (trust : Bool) (timeout : Nat) (fmf : Bool)
    (wantModel : Bool := true) : TermElabM (TSyntax `tactic) := do
  let bool (b : Bool) : Ident := mkIdent (if b then ``true else ``false)
  let options ← `([("finite-model-find", $(Syntax.mkStrLit (toString fmf))),
    ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")])
  let smt ← `(tactic|
    smt
      ($(mkIdent `trust):ident := $(bool trust):ident)
      ($(mkIdent `embedBool):ident := $(bool !trust):ident)
      ($(mkIdent `model):ident := $(bool wantModel):ident)
      ($(mkIdent `timeout):ident := $(mkIdent ``Option.some) $(quote timeout))
      ($(mkIdent `extraSolverOptions):ident := $options)
      [$[$hyps:ident],*])
  `(tactic| open $(mkIdent `Classical):ident in $smt:tactic)

/-! ### Goals -/

/-- The hypotheses to hand to the solver: the propositions of the context that are not
`Nonempty` or `Inhabited` facts, in order. -/
def solverHyps (g : MVarId) : MetaM (Array LocalDecl) := g.withContext do
  (← getLCtx).decls.toArray.filterMapM fun
    | some decl => do
      if decl.isImplementationDetail then return none
      let ty ← whnf decl.type
      if ty.isAppOf ``Nonempty || ty.isAppOf ``Inhabited then return none
      return if ← isProp ty then some decl else none
    | none => return none

/-- Split the hypothesis `h : A ∧ (B ∧ …)` into one hypothesis per conjunct, in order. -/
partial def splitConjunction (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  unless (← whnfR (← h.getType)).isAppOfArity ``And 2 do return g
  let #[sub] ← g.cases h | return g
  let #[l, r] := sub.fields | return sub.mvarId
  splitConjunction (← splitConjunction sub.mvarId l.fvarId!) r.fvarId!

/-- Split the last hypothesis, the conjunction of a diagram's literals, so that the literals are
the last hypotheses. -/
def splitTrailingConjunction (g : MVarId) : MetaM MVarId := g.withContext do
  let props ← (← getLCtx).decls.toArray.filterMapM fun
    | some decl => do
      return if !decl.isImplementationDetail && (← isProp decl.type) then some decl else none
    | none => return none
  let some decl := props.back? | return g
  if (← whnfR decl.type).isAppOfArity ``And 2 then splitConjunction g decl.fvarId else return g

/-- Unfold `CanonicalField` and `IteratedArrow` in the goal and the hypotheses, which lean-smt
cannot translate when they occur as type arguments (`total := total + 1` on an `Int` field). -/
def unfoldCanonicalFields (g : MVarId) : MetaM MVarId := g.withContext do
  let unfold (e : Expr) : MetaM Expr := Meta.transform e (post := fun e ↦ do
    if e.isAppOfArity ``Veil.CanonicalField 2 || e.isAppOfArity ``Veil.IteratedArrow 2 then
      let e' ← whnfR e
      if e' != e then return .visit e'
    return .continue)
  let mut g ← g.replaceTargetDefEq (← unfold (← g.getType))
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← unfold decl.type
    if ty != decl.type then g ← g.replaceLocalDeclDefEq decl.fvarId ty
  return g

/-- If the goal is `¬ C`, introduce `C` and split it. -/
def introAndSplit (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← g.getType)
  unless ty.isAppOfArity ``Not 1 || ty.isArrow do return g
  let (h, g') ← g.intro1
  splitConjunction g' h

/-- The goal the solver sees after preprocessing, with the hypotheses to hand it. When
`coreLits > 0`, the last `coreLits` hypotheses are the literals of a diagram. -/
def prepareGoal (g : MVarId) (coreLits : Nat) : MetaM (MVarId × Array LocalDecl) := do
  let g ← introAndSplit g
  let g ← if coreLits > 0 then splitTrailingConjunction g else pure g
  let g ← unfoldCanonicalFields g
  return (g, ← solverHyps g)

/-! ### Running a statement -/

/-- Elaborate a statement, failing on `sorry` and metavariables. -/
def elabStatement (stmt : Term) : TermElabM (Except String Expr) := do
  try
    let ty ← Term.withoutErrToSorry do
      let ty ← elabTerm stmt (some (mkSort .zero))
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars ty
    if ty.hasSorry || ty.hasMVar || ty.hasLevelMVar then
      return .error "statement contains sorry or metavariables"
    return .ok ty
  catch e => return .error (← e.toMessageData.toString)

/-- Run `x`, recovering from runtime exceptions with their message. -/
def catchRuntime (x : TermElabM α) : TermElabM (Except String α) :=
  tryCatchRuntimeEx (.ok <$> x) fun e ↦ return .error (← e.toMessageData.toString)

/-- The result of a run of the `smt` tactic that sent no answer: lean-smt reports `unknown`,
timeouts included, by throwing. -/
def resultOfSolverError : Except String Unit → QueryResult
  | .error e =>
    if (e.splitOn "unable to prove goal. Try providing more hints. Reason:").length > 1
      || (unknownExplanation? e).isSome then .unknown s!"{solverUnknownPrefix}: {e.take 300}"
    else .error s!"solver produced no output: {e.take 300}"
  | .ok _ => .error "solver produced no output"

/-- Discharge a closed statement over `steps` transitions. When `coreLits > 0`, its last
`coreLits` conjuncts are diagram literals, and an `unsat` answer comes with the indices of those
in the unsat core. -/
def runStatementOnce (mod : Veil.Module) (stmt : Term) (steps coreLits : Nat) (wantModel : Bool) :
    TermElabM (QueryResult × Option (Array Nat)) := do
  let opts ← getOptions
  let fault ← failQueryAt
  let trust := veil.synthesizer.trust.get opts && coreLits == 0
  let ch ← Std.CloseableChannel.new
  let name ← mkFreshUserName `synthQuery
  let _ ← Smt.initAsyncState name (some ch)
  let tElab ← IO.monoMsNow
  let ty? ← elabStatement stmt
  notePhase (fun p dt ↦ { p with elabMs := p.elabMs + dt }) tElab
  let ty ← match ty? with
    | .ok ty => pure ty
    | .error e => return (.error s!"statement failed to elaborate: {e.take 300}", none)
  if fault == some ("throw", steps) then throwError (injectedQueryFailure "throw" steps)
  let mv ← mkFreshExprMVar ty
  let tPre ← IO.monoMsNow
  let preprocess ← preprocessTactic (← TrNorm.available mod) trust
  let goals? ← catchRuntime (Tactic.run mv.mvarId! (Tactic.evalTactic preprocess))
  notePhase (fun p dt ↦ { p with preprocessMs := p.preprocessMs + dt }) tPre
  let goals ← match goals? with
    | .ok gs => pure gs
    | .error e => return (.unknown s!"preprocessing failed: {e.take 300}", none)
  let some g₀ := goals.head? | do
    -- Preprocessing alone closed the goal.
    let pf ← instantiateMVars mv
    return (.unsat ty pf (pf.hasSorry || pf.hasMVar), some #[])
  let (g, hyps) ← prepareGoal g₀ coreLits
  let litHyps := if coreLits > 0 && hyps.size ≥ coreLits then
    (hyps.extract (hyps.size - coreLits) hyps.size).map (·.fvarId) else #[]
  if coreLits > 0 && (← isTracingEnabledFor `veil.synthesizer.debug) then
    g.withContext do
      let mut msg :=
        m!"{hyps.size} solver hypotheses for {coreLits} literals; goal: {← g.getType}\n"
      for d in hyps do msg := msg ++ m!"  {d.userName} : {d.type}\n"
      logInfo msg
  let smt ← smtTactic (hyps.map (mkIdent ·.userName)) trust (veil.smt.timeout.get opts)
    (veil.smt.finiteModelFind.get opts) wantModel
  let tSmt ← IO.monoMsNow
  -- Steps lean-smt cannot reconstruct remain as goals; they are admitted, so the proof carries
  -- `sorry` and the answer counts as trusted.
  let solved ← catchRuntime do
    for r in ← Tactic.run g (Tactic.evalTactic smt) do r.admit (synthetic := false)
  let outputs ← collectSmtOutputs ch name
  notePhase (fun p dt ↦ { p with smtMs := p.smtMs + dt }) tSmt
  let mut result := resultOfSolverError solved
  let mut core := none
  for (_, o) in outputs do
    match o with
    | .result (.sat none) =>
      result := if wantModel then .satUndecoded "the solver returned no model" else .sat .null
    | .result (.sat (some m)) =>
      let tDecode ← IO.monoMsNow
      result ← if fault == some ("undecoded", steps) then
          pure (.satUndecoded (injectedQueryFailure "undecoded" steps))
        else
          match ← catchRuntime do unsafe (← buildTraceFromModel m mod steps).toJson with
          | .ok j => pure (.sat j)
          | .error e => pure (.satUndecoded s!"{e.take 300}")
      notePhase (fun p dt ↦ { p with decodeMs := p.decodeMs + dt }) tDecode
    | .result (.unsat _ used) =>
      let pf ← instantiateMVars mv
      result := .unsat ty pf (pf.hasSorry || pf.hasMVar)
      if coreLits > 0 && litHyps.size == coreLits then
        let usedIds := used.filterMap fun e ↦ if e.isFVar then some e.fvarId! else none
        core := some <| (Array.range coreLits).filter (usedIds.contains litHyps[·]!)
    | .exception e =>
      let msg ← e.toMessageData.toString
      result := if (unknownExplanation? msg).isSome then .unknown s!"{solverUnknownPrefix}: {msg}"
        else .error msg
    | _ => pure ()
  return (result, core)

/-- Run `x` under the per-query heartbeat budget, then restore lean-smt's async state, which
`runStatementOnce` points at its own result channel. -/
def withQueryBudget (x : TermElabM α) : TermElabM α := do
  let saved := Smt.asyncState.getState (← getEnv)
  withCurrHeartbeats <|
    withTheReader Core.Context (fun c ↦ { c with maxHeartbeats := 4000000 * 1000 })
    (try x finally modifyEnv (Smt.asyncState.modifyState · fun _ ↦ saved))

/-- Discharge a statement over `steps` transitions (see `runStatementOnce`). A runtime exception
(heartbeats, recursion depth) is `unknown`; any other exception is a bug and is rethrown. An
unreadable core query is asked again without its core, and a proof lean-smt cannot replay is
asked again trusting the solver. -/
def runStatement (mod : Veil.Module) (stmt : Term) (steps : Nat) (coreLits : Nat := 0)
    (wantModel : Bool := true) : TermElabM (QueryResult × Option (Array Nat)) := do
  if (← failQueryAt) == some ("unknown", steps) then
    return (.unknown (injectedQueryFailure "unknown" steps), none)
  let run (lits : Nat) : TermElabM (QueryResult × Option (Array Nat)) :=
    withQueryBudget <| tryCatchRuntimeEx (runStatementOnce mod stmt steps lits wantModel) fun e ↦ do
      unless e.isRuntime do throw e
      return (.unknown s!"query exceeded its budget: {(← e.toMessageData.toString).take 200}", none)
  let mut r ← run coreLits
  if let (.error e, _) := r then
    if coreLits > 0 && !e.startsWith "statement failed to elaborate" then r ← run 0
  if let (.error e, _) := r then
    let replayFailed := (e.splitOn "Failed to reconstruct").length > 1
    if !veil.synthesizer.trust.get (← getOptions) && replayFailed then
      r ← withOptions (veil.synthesizer.trust.set · true) (run 0)
  return r

end Veil.Synthesizer
