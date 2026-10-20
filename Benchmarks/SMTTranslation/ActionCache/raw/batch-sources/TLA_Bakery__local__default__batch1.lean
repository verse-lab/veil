module

public import Veil

set_option Elab.async false
section

open Lean Elab Tactic Meta Veil

meta def symbolicBenchEvent (event phase status : String) (elapsed : Nat := 0)
    (extra : List (String × Json) := []) : CoreM Unit := do
  let j := Json.mkObj ([
    ("event", toJson event), ("phase", toJson phase), ("status", toJson status),
    ("elapsed_ms", toJson elapsed), ("mono_ms", toJson (← IO.monoMsNow))] ++ extra)
  IO.FS.withFile (System.FilePath.mk ((← getOptions).get `symbolicBench.eventPath "")) .append fun h => h.putStrLn j.compress

meta partial def symbolicBenchIntroData (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := target.consumeMData | return goal
  if ← isProp domain then return goal
  let (_, next) ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1
  symbolicBenchIntroData next

elab "symbolic_bench_intro_data" : tactic => do
  liftMetaTactic1 fun goal => return some (← symbolicBenchIntroData goal)

elab "symbolic_bench_phase " label:str t:tactic : tactic => do
  if (← getGoals).isEmpty then
    symbolicBenchEvent "stage" label.getString "skipped_goal_closed"
  else
    symbolicBenchEvent "stage" label.getString "begin"
    let start ← IO.monoMsNow
    let hbStart ← IO.getNumHeartbeats
    try
      withoutRecover <| evalTactic t
      symbolicBenchEvent "stage" label.getString "complete" ((← IO.monoMsNow) - start)
        [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    catch ex =>
      symbolicBenchEvent "stage" label.getString "failed" ((← IO.monoMsNow) - start)
        [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
      throw ex

meta def symbolicBenchMetaPhase {α : Type} (label : String) (computation : MetaM α) : MetaM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  let hbStart ← IO.getNumHeartbeats
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
    throw ex

meta def symbolicBenchTacticPhase {α : Type} (label : String) (computation : TacticM α) : TacticM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  let hbStart ← IO.getNumHeartbeats
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
    throw ex

elab "symbolic_bench_extract " eventPath:str path:str t:tactic : tactic => do
  withOptions (fun opts => opts.set `symbolicBench.eventPath eventPath.getString) do
    symbolicBenchEvent "pipeline" "pipeline" "begin" 0 [
      ("maxHeartbeats", toJson (maxHeartbeats.get (← getOptions))),
      ("maxRecDepth", toJson (maxRecDepth.get (← getOptions)))]
    let start ← IO.monoMsNow
    withoutRecover <| evalTactic t
    symbolicBenchEvent "milestone" "preprocessing" "complete" ((← IO.monoMsNow) - start)
    if (← getGoals).isEmpty then
      symbolicBenchEvent "pipeline" "pipeline" "discharged" ((← IO.monoMsNow) - start)
    else
      Veil.withBackwardsCompatibility <| withMainContext do
        let (mv, hs) ← symbolicBenchTacticPhase "cleanup" do
          let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
          let goal ← getMainGoal
          let mv := (← Meta.mkFreshExprMVar (← goal.getType)).mvarId!
          let mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
          return (mv, hs)
        let mut mv := mv
        let mut hs := hs
        let steps : Array (String × (MVarId → Array Expr → MetaM Smt.Preprocess.Result)) := #[
          ("pushHints", Smt.Preprocess.pushHintsToCtx),
          ("smt-intros", Smt.Preprocess.intros),
          ("negateGoal", Smt.Preprocess.negateGoal),
          ("normalize", Smt.Preprocess.normalize),
          ("embedding", Smt.Preprocess.embeddingWithConfig { embedBool := false })]
        for (label, step) in steps do
          let result ← symbolicBenchMetaPhase label <| mv.withContext <| step mv hs
          mv := result.mv
          hs := result.hs
        let cmds ← symbolicBenchMetaPhase "translate" <| mv.withContext do
          let (fvNames, _) ← Smt.genUniqueFVarNames
          Smt.prepareSmtQuery hs.toList fvNames
        let query ← symbolicBenchMetaPhase "serialize" do
          let query := Smt.Translate.Command.cmdsAsQuery (.setLogic "ALL" :: cmds ++ [.checkSat])
          IO.FS.writeFile path.getString query
          return query
        symbolicBenchEvent "pipeline" "pipeline" "complete" ((← IO.monoMsNow) - start)
          [("bytes", toJson query.utf8ByteSize), ("commands", toJson cmds.length)]
    -- Deliberately abandon the measurement declaration; no theorem is admitted.
    throwError "SYMBOLIC_BMC_EXTRACTION_COMPLETE: query extraction only; no proof claimed"

end
set_option veil.experimental.bmcCache false

veil module Bakery

param maxProc : Nat
param maxNum : Nat

abbrev TicketNum (maxNum : Nat) := Fin (maxNum + 1)
abbrev ProcTy (maxProc : Nat) := Fin (maxProc + 1)

enum pc_state = { ncs, e1, e2, e3, e4, w1, w2, cs, exit }

-- Changed: unchecked is now a TSet-based ProcessSet instead of a relation
type ProcessSet
instantiate pSet : TSet (ProcTy maxProc) ProcessSet

function num          : ProcTy maxProc → TicketNum maxNum
relation flag         : ProcTy maxProc → Bool
function unchecked    : ProcTy maxProc → ProcessSet
function max          : ProcTy maxProc → TicketNum maxNum
function nxt          : ProcTy maxProc → ProcTy maxProc
function pc           : ProcTy maxProc → pc_state

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

ghost relation prec (a b : TicketNum maxNum × ProcTy maxProc) :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

after_init {
  let zeroNum := ⟨0, Nat.zero_lt_succ maxNum⟩
  let firstProc := ⟨0, Nat.zero_lt_succ maxProc⟩
  num P := zeroNum
  flag P := false
  unchecked P := pSet.empty
  max P := zeroNum
  nxt P := firstProc
  pc P := ncs
}

action evtNCS (self : ProcTy maxProc) {
  require pc self = ncs
  pc self := e1
}

action evtE1 (self : ProcTy maxProc) {
  require pc self = e1
  let branch ← pick Bool
  if branch then
    flag self := !flag self
    pc self := e1
  else
    flag self := true
    unchecked self := pSet.remove self (pSet.ofList (Veil.Enumeration.allValues))   -- NOTE: see comment above
    max self := ⟨0, Nat.zero_lt_succ maxNum⟩
    pc self := e2
}

action evtE2 (self : ProcTy maxProc) {
  require pc self = e2
  if ¬ pSet.isEmpty (unchecked self) then
    let i ← pick { i // i ∈ unchecked self }
    let i := i.val
    unchecked self := pSet.remove i (unchecked self)
    let num_i := num i
    let max_self := max self
    if max_self < num_i then
      max self := num_i
    pc self := e2
  else
    pc self := e3
}

action evtE3 (self : ProcTy maxProc) {
  require pc self = e3
  let branch ← pick Bool
  if branch then
    let k ← pick (TicketNum maxNum)
    num self := k
    pc self := e3
  else
    let j :| max self < j
    num self := j
    pc self := e4
}

action evtE4 (self : ProcTy maxProc) {
  require pc self = e4
  let branch ← pick Bool
  if branch then
    flag self := !flag self
    pc self := e4
  else
    flag self := false
    unchecked self := pSet.remove self (pSet.ofList (Veil.Enumeration.allValues))   -- NOTE: see comment above
    pc self := w1
}

action evtW1 (self : ProcTy maxProc) {
  require pc self = w1
  if ¬ pSet.isEmpty (unchecked self) then
    let i ← pick { i // i ∈ unchecked self }
    let i := i.val
    nxt self := i
    assume ¬ flag (nxt self)
    pc self := w2
  else
    pc self := cs
}

action evtW2 (self : ProcTy maxProc) {
  require pc self = w2
  let nxt_self := nxt self
  let num_self := num self
  let num_nxt_self := num nxt_self
  require num_nxt_self.val = 0 ∨ prec (num_self, self) (num_nxt_self, nxt_self)
  unchecked self := pSet.remove nxt_self (unchecked self)
  pc self := w1
}

action evtCS (self : ProcTy maxProc) {
  require pc self = cs
  pc self := exit
}

action evtExit (self : ProcTy maxProc) {
  require pc self = exit
  let branch ← pick Bool
  if branch then
    let k ← pick (TicketNum maxNum)
    num self := k
    pc self := exit
  else
    num self := ⟨0, Nat.zero_lt_succ maxNum⟩
    pc self := ncs
}

ghost relation num_gt_zero (i : ProcTy maxProc) := ⟨0, Nat.zero_lt_succ maxNum⟩ < num i

ghost relation pc_ncs_e1_exit (j : ProcTy maxProc) := pc j ∈ [ncs, e1, exit]

ghost relation pc_ex (i j : ProcTy maxProc) :=
  pc j = e2 ∧ (i ∈ unchecked j ∨ num i ≤ max j)

ghost relation pc_e3 (i j : ProcTy maxProc) :=
  pc j = e3 ∧ num i ≤ max j

ghost relation pc_e4_w1_w2 (i j : ProcTy maxProc) :=
  pc j ∈ [e4, w1, w2] ∧
  prec (num i, i) (num j, j) ∧
  (pc j ∈ [w1, w2] → i ∈ unchecked j)

ghost relation before (i j : ProcTy maxProc) :=
  num_gt_zero i ∧ (pc_ncs_e1_exit j ∨ pc_ex i j ∨ pc_e3 i j ∨ pc_e4_w1_w2 i j)

ghost relation p1_non_zero_num (i : ProcTy maxProc) :=
  pc i ∈ [e4, w1, w2, cs] → (num i).val ≠ 0

ghost relation p2_flag_e2_e3 (i : ProcTy maxProc) :=
  pc i ∈ [e2, e3] → flag i

ghost relation p3_nxt_not_self (i : ProcTy maxProc) :=
  pc i = w2 → nxt i ≠ i

ghost relation p4_unchecked_not_self (i : ProcTy maxProc) :=
  pc i ∈ [w1, w2] → i ∉ unchecked i

ghost relation p5_critical_section (i : ProcTy maxProc) :=
  pc i ∈ [w1, w2] → ∀ j, j ≠ i → j ∉ unchecked i → before i j

ghost relation p6_nxt_e2_e3 (i : ProcTy maxProc) :=
  pc i = w2 ∧
  ((pc (nxt i) = e2 ∧ i ∉ unchecked (nxt i)) ∨ pc (nxt i) = e3) →
    num i ≤ max (nxt i)

ghost relation p7_cs_precedes_all (i : ProcTy maxProc) :=
  pc i = cs → ∀ j, j ≠ i → before i j

invariant [iinv] ∀ i,
  p1_non_zero_num i ∧
  p2_flag_e2_e3 i ∧
  p3_nxt_not_self i ∧
  p4_unchecked_not_self i ∧
  p5_critical_section i ∧
  p6_nxt_e2_e3 i ∧
  p7_cs_precedes_all i

safety [mutual_exclusion] I ≠ J → ¬ (pc I = cs ∧ pc J = cs)

set_option maxHeartbeats 2500000

#gen_spec
run_cmd discard <| _root_.Veil.Verifier.waitFilteredSync _root_.Veil.Verifier.isDoesNotThrow

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-action-cache/results/batch-events/TLA_Bakery__local__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ i j, i ≠ j ∧ pc i = cs ∧ pc j = cs)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_Bakery__d1__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_Bakery__d1__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any 2 actions
  assert (∃ i j, i ≠ j ∧ pc i = cs ∧ pc j = cs)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_Bakery__d2__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_Bakery__d2__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 4 actions
  assert (∃ i j, i ≠ j ∧ pc i = cs ∧ pc j = cs)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_Bakery__d4__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_Bakery__d4__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 8 actions
  assert (∃ i j, i ≠ j ∧ pc i = cs ∧ pc j = cs)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_Bakery__d8__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_Bakery__d8__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 16 actions
  assert (∃ i j, i ≠ j ∧ pc i = cs ∧ pc j = cs)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_Bakery__d16__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_Bakery__d16__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 32 actions
  assert (∃ i j, i ≠ j ∧ pc i = cs ∧ pc j = cs)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_Bakery__d32__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_Bakery__d32__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_Bakery__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end Bakery
