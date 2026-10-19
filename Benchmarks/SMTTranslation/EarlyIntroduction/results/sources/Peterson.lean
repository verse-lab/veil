module

public import Veil

open Lean Elab Tactic Meta Veil

meta partial def introDataPrefix (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := target.consumeMData | return goal
  if ← isProp domain then return goal
  let (_, goal') ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1
  introDataPrefix goal'

elab "intro_data_prefix" : tactic => do
  liftMetaTactic1 fun goal => return some (← introDataPrefix goal)


meta def benchPrint (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

elab "bench_stage " key:str label:str t:tactic : tactic => do
  let start ← IO.monoMsNow
  try
    evalTactic t
    benchPrint s!"STAGE {key.getString} {label.getString} ms={(← IO.monoMsNow)-start}"
  catch ex =>
    benchPrint s!"FAILED {key.getString} {label.getString} ms={(← IO.monoMsNow)-start}: {← ex.toMessageData.toString}"
    throw ex

elab "bench_run " label:str marker:str t:tactic : tactic => do
  if ← System.FilePath.pathExists marker.getString then
    benchPrint s!"RUN_SKIPPED {label.getString} prior_failure"
    evalTactic (← `(tactic| sorry))
  else
    benchPrint s!"RUN_BEGIN {label.getString}"
    let saved ← saveState
    try
      evalTactic t
      benchPrint s!"RUN_COMPLETE {label.getString}"
    catch _ =>
      saved.restore
      IO.FS.writeFile marker.getString "failed"
      benchPrint s!"RUN_FAILED {label.getString}"
    evalTactic (← `(tactic| sorry))

elab "bench_smt_pipeline " key:str path:str : tactic => do
  let saved ← saveState
  try
    withMainContext do
      let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
      let goal ← getMainGoal
      let mut mv := (← Meta.mkFreshExprMVar (← goal.getType)).mvarId!
      mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
      let mut hs := hs
      let steps : Array (String × (MVarId → Array Expr → MetaM Smt.Preprocess.Result)) := #[
        ("pushHints", Smt.Preprocess.pushHintsToCtx),
        ("smt-intros", Smt.Preprocess.intros),
        ("negateGoal", Smt.Preprocess.negateGoal),
        ("normalize", Smt.Preprocess.normalize),
        ("embedding", Smt.Preprocess.embeddingWithConfig { embedBool := false })]
      for (name, step) in steps do
        let start ← IO.monoMsNow
        let r ← mv.withContext <| step mv hs
        mv := r.mv
        hs := r.hs
        benchPrint s!"SMT_STAGE {key.getString} {name} ms={(← IO.monoMsNow)-start}"
      let start ← IO.monoMsNow
      let cmds ← mv.withContext do
        let (fvNames, _) ← Smt.genUniqueFVarNames
        Smt.prepareSmtQuery hs.toList fvNames
      benchPrint s!"SMT_STAGE {key.getString} translate ms={(← IO.monoMsNow)-start} commands={cmds.length}"
      let start ← IO.monoMsNow
      let query := Smt.Translate.Command.cmdsAsQuery (.setLogic "ALL" :: cmds ++ [.checkSat])
      IO.FS.writeFile path.getString query
      benchPrint s!"SMT_STAGE {key.getString} serialize ms={(← IO.monoMsNow)-start} bytes={query.utf8ByteSize}"
      benchPrint s!"PIPELINE_COMPLETE {key.getString}"
  catch ex =>
    benchPrint s!"PIPELINE_FAILED {key.getString}: {← ex.toMessageData.toString}"
  saved.restore


veil module Peterson

-- -----------------------------------------------------------------------------
-- This module contains the specification for Peterson's Lock Algorithm.
-- https://en.wikipedia.org/wiki/Peterson%27s_algorithm
--
-- TLA+ Source :
-- https://github.com/tlaplus/Examples/blob/9ece37b2e6d5cab0de16582ea81733ce5f586a84/specifications/locks_auxiliary_vars/Peterson.tla
-- ---------------------------------- -------------------------------------------


/-
Peterson Algorithm is a two-thread/process concurrent algorithm, so we only
need to define two processes, `P1` and `P2`, here.
* `turn` is used as a flag that indicates which process
has the right to enter the critical section.
* `wantEnter p` is used to indicate whether process `p` wants to enter the critical section.
* `pc` is short for program counter, which indicates the state of each process.
-/
enum Phase = { idle, request, yieldTurn, waiting, critical, release }
enum Process = { P1, P2 }
individual turn : Process
relation wantEnter : Process → Bool
relation pc : Process → Phase → Bool
#gen_state



after_init {
  wantEnter P := false
  turn := P1
  pc P S := S == idle

}

action beginRequest (self : Process) {
  require pc self idle
  pc self S := S == request
}


/-
This action states that the process begin to
have the willing to enter the critical section.
-/
action prepareYield (self : Process) {
  require pc self request
  wantEnter self := true
  pc self S := S == yieldTurn
}


/-
This is the key step to make it successful to achieve mutual exclusion.
When a process wants to enter the critical section,
it sets the `turn` flag to the other process politely,
indicating that it is willingness to yield
the right to enter the critical section to the other process.
 -/
action yieldAndWaiting (self : Process) {
  require pc self yieldTurn
  turn := if self = P1 then P2 else P1
  pc self S := S == waiting
}


/-
Now, finally the process can enter the critical section.
The condition is that either the other process does not want to enter
the critical section, or it is this process's turn.
-/
action enterCS (self : Process) {
  require pc self waiting
  require ¬ wantEnter (if self = P1 then P2 else P1) ∨ turn = self
  pc self S := S == critical
}


/- The process can leave the critical section whenever it would like to. -/
action releaseCS (self : Process) {
  require pc self critical
  pc self S := S == release
}


/-
After leaving the critical section, the process will return
to the initial state `idle`.
 -/
action returnIdle (self : Process) {
  require pc self release
  wantEnter self := false
  pc self S := S == idle
}


/-
This is usually one of the most important properties of
a concurrent programming algorithm, which says that
no two processes can be in their critical sections at the same time.
-/
ghost relation lockcs (i : Process) := pc i critical ∨ pc i release

safety [mutual_exclusion]
  ∀ i j, i ≠ j → ¬(lockcs i ∧ lockcs j)


-- Some helpful invariants
invariant [pc_total] pc P idle ∨ pc P request ∨ pc P yieldTurn ∨ pc P waiting ∨ pc P critical ∨ pc P release
invariant [unique_phase] pc P S ∧ pc P T → S = T
invariant [flag_consistency] ∀p, wantEnter p ↔ (pc p yieldTurn ∨ pc p waiting ∨ pc p critical ∨ pc p release)
invariant [progress_critical]
  ∀p, (pc p critical ∨ pc p release) →
  (turn = p ∨
    (pc (if p = P1 then P2 else P1) idle ∨
     pc (if p = P1 then P2 else P1) request ∨
     pc (if p = P1 then P2 else P1) yieldTurn))

#gen_spec
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

unsat trace [bench_current_2_1] {
  any 2 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_2_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_2_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_2_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_2_1" "intros" veil_intros
    bench_stage "Peterson_current_2_1" "destruct" veil_destruct
    bench_stage "Peterson_current_2_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_2_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_2_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_current_2_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_current_2_1.smt2"
  )

unsat trace [bench_early_2_1] {
  any 2 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_2_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_2_1" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_2_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_2_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_2_1" "intros" veil_intros
    bench_stage "Peterson_early_2_1" "destruct" veil_destruct
    bench_stage "Peterson_early_2_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_2_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_2_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_early_2_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_early_2_1.smt2"
  )

unsat trace [bench_early_2_2] {
  any 2 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_2_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_2_2" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_2_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_2_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_2_2" "intros" veil_intros
    bench_stage "Peterson_early_2_2" "destruct" veil_destruct
    bench_stage "Peterson_early_2_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_2_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_2_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_2_2] {
  any 2 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_2_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_2_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_2_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_2_2" "intros" veil_intros
    bench_stage "Peterson_current_2_2" "destruct" veil_destruct
    bench_stage "Peterson_current_2_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_2_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_2_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_2_3] {
  any 2 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_2_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_2_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_2_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_2_3" "intros" veil_intros
    bench_stage "Peterson_current_2_3" "destruct" veil_destruct
    bench_stage "Peterson_current_2_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_2_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_2_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_2_3] {
  any 2 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_2_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_2_3" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_2_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_2_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_2_3" "intros" veil_intros
    bench_stage "Peterson_early_2_3" "destruct" veil_destruct
    bench_stage "Peterson_early_2_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_2_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_2_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_4_1] {
  any 4 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_4_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_4_1" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_4_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_4_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_4_1" "intros" veil_intros
    bench_stage "Peterson_early_4_1" "destruct" veil_destruct
    bench_stage "Peterson_early_4_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_4_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_4_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_early_4_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_early_4_1.smt2"
  )

unsat trace [bench_current_4_1] {
  any 4 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_4_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_4_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_4_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_4_1" "intros" veil_intros
    bench_stage "Peterson_current_4_1" "destruct" veil_destruct
    bench_stage "Peterson_current_4_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_4_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_4_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_current_4_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_current_4_1.smt2"
  )

unsat trace [bench_current_4_2] {
  any 4 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_4_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_4_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_4_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_4_2" "intros" veil_intros
    bench_stage "Peterson_current_4_2" "destruct" veil_destruct
    bench_stage "Peterson_current_4_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_4_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_4_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_4_2] {
  any 4 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_4_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_4_2" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_4_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_4_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_4_2" "intros" veil_intros
    bench_stage "Peterson_early_4_2" "destruct" veil_destruct
    bench_stage "Peterson_early_4_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_4_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_4_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_4_3] {
  any 4 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_4_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_4_3" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_4_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_4_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_4_3" "intros" veil_intros
    bench_stage "Peterson_early_4_3" "destruct" veil_destruct
    bench_stage "Peterson_early_4_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_4_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_4_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_4_3] {
  any 4 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_4_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_4_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_4_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_4_3" "intros" veil_intros
    bench_stage "Peterson_current_4_3" "destruct" veil_destruct
    bench_stage "Peterson_current_4_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_4_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_4_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_8_1] {
  any 8 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_8_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_8_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_8_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_8_1" "intros" veil_intros
    bench_stage "Peterson_current_8_1" "destruct" veil_destruct
    bench_stage "Peterson_current_8_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_8_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_8_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_current_8_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_current_8_1.smt2"
  )

unsat trace [bench_early_8_1] {
  any 8 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_8_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_8_1" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_8_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_8_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_8_1" "intros" veil_intros
    bench_stage "Peterson_early_8_1" "destruct" veil_destruct
    bench_stage "Peterson_early_8_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_8_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_8_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_early_8_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_early_8_1.smt2"
  )

unsat trace [bench_early_8_2] {
  any 8 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_8_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_8_2" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_8_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_8_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_8_2" "intros" veil_intros
    bench_stage "Peterson_early_8_2" "destruct" veil_destruct
    bench_stage "Peterson_early_8_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_8_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_8_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_8_2] {
  any 8 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_8_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_8_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_8_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_8_2" "intros" veil_intros
    bench_stage "Peterson_current_8_2" "destruct" veil_destruct
    bench_stage "Peterson_current_8_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_8_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_8_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_8_3] {
  any 8 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_8_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_8_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_8_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_8_3" "intros" veil_intros
    bench_stage "Peterson_current_8_3" "destruct" veil_destruct
    bench_stage "Peterson_current_8_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_8_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_8_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_8_3] {
  any 8 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_8_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_8_3" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_8_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_8_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_8_3" "intros" veil_intros
    bench_stage "Peterson_early_8_3" "destruct" veil_destruct
    bench_stage "Peterson_early_8_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_8_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_8_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_16_1] {
  any 16 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_16_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_16_1" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_16_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_16_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_16_1" "intros" veil_intros
    bench_stage "Peterson_early_16_1" "destruct" veil_destruct
    bench_stage "Peterson_early_16_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_16_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_16_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_early_16_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_early_16_1.smt2"
  )

unsat trace [bench_current_16_1] {
  any 16 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_16_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_16_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_16_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_16_1" "intros" veil_intros
    bench_stage "Peterson_current_16_1" "destruct" veil_destruct
    bench_stage "Peterson_current_16_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_16_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_16_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_current_16_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_current_16_1.smt2"
  )

unsat trace [bench_current_16_2] {
  any 16 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_16_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_16_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_16_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_16_2" "intros" veil_intros
    bench_stage "Peterson_current_16_2" "destruct" veil_destruct
    bench_stage "Peterson_current_16_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_16_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_16_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_16_2] {
  any 16 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_16_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_16_2" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_16_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_16_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_16_2" "intros" veil_intros
    bench_stage "Peterson_early_16_2" "destruct" veil_destruct
    bench_stage "Peterson_early_16_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_16_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_16_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_16_3] {
  any 16 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_16_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_16_3" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_16_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_16_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_16_3" "intros" veil_intros
    bench_stage "Peterson_early_16_3" "destruct" veil_destruct
    bench_stage "Peterson_early_16_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_16_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_16_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_16_3] {
  any 16 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_16_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_16_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_16_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_16_3" "intros" veil_intros
    bench_stage "Peterson_current_16_3" "destruct" veil_destruct
    bench_stage "Peterson_current_16_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_16_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_16_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_32_1] {
  any 32 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_32_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_32_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_32_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_32_1" "intros" veil_intros
    bench_stage "Peterson_current_32_1" "destruct" veil_destruct
    bench_stage "Peterson_current_32_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_32_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_32_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_current_32_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_current_32_1.smt2"
  )

unsat trace [bench_early_32_1] {
  any 32 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_32_1" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_32_1" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_32_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_32_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_32_1" "intros" veil_intros
    bench_stage "Peterson_early_32_1" "destruct" veil_destruct
    bench_stage "Peterson_early_32_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_32_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_32_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "Peterson_early_32_1" "/tmp/veil-early-intro-multi/results/queries/Peterson_early_32_1.smt2"
  )

unsat trace [bench_early_32_2] {
  any 32 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_32_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_32_2" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_32_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_32_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_32_2" "intros" veil_intros
    bench_stage "Peterson_early_32_2" "destruct" veil_destruct
    bench_stage "Peterson_early_32_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_32_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_32_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_32_2] {
  any 32 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_32_2" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_32_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_32_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_32_2" "intros" veil_intros
    bench_stage "Peterson_current_32_2" "destruct" veil_destruct
    bench_stage "Peterson_current_32_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_32_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_32_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_32_3] {
  any 32 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_current_32_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_current" (
    bench_stage "Peterson_current_32_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_current_32_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_current_32_3" "intros" veil_intros
    bench_stage "Peterson_current_32_3" "destruct" veil_destruct
    bench_stage "Peterson_current_32_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_current_32_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_current_32_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_32_3] {
  any 32 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  bench_run "Peterson_early_32_3" "/tmp/veil-early-intro-multi/results/markers/Peterson_early" (
    bench_stage "Peterson_early_32_3" "early_intros" intro_data_prefix
    bench_stage "Peterson_early_32_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "Peterson_early_32_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "Peterson_early_32_3" "intros" veil_intros
    bench_stage "Peterson_early_32_3" "destruct" veil_destruct
    bench_stage "Peterson_early_32_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "Peterson_early_32_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "Peterson_early_32_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

end Peterson
