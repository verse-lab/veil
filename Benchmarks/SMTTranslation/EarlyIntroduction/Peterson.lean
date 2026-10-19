module

public import Veil

open Lean Elab Tactic Meta Veil
elab "check_solver_outcome " label:str : tactic => withMainContext do
  let start ← IO.monoMsNow
  try
    let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
    let original ← getMainGoal
    let mut mv := (← Meta.mkFreshExprMVar (← original.getType)).mvarId!
    mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
    let steps := #[Smt.Preprocess.pushHintsToCtx, Smt.Preprocess.intros, Smt.Preprocess.negateGoal,
      Smt.Preprocess.normalize, Smt.Preprocess.embeddingWithConfig { embedBool := false }]
    let ⟨_, hs, normalizedGoal⟩ ← mv.withContext <| Smt.Preprocess.applySteps mv hs steps
    let cmds ← normalizedGoal.withContext do
      let (fvNames, _) ← Smt.genUniqueFVarNames
      Smt.prepareSmtQuery hs.toList fvNames
    let cmds := Smt.Translate.Command.setLogic "ALL" :: cmds
    let query := Smt.Translate.Command.cmdsAsQuery cmds
    let path := "/tmp/veil-early-intro-multi/" ++ label.getString ++ ".smt2"
    IO.FS.writeFile path (Smt.Translate.Command.cmdsAsQuery (cmds ++ [.checkSat]))
    let prepared ← IO.monoMsNow
    let options := Smt.defaultSolverOptions ++ [("finite-model-find", "true"),
      ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
    let result ← Smt.solve query (some 10) false options
    let status := match result with
      | .ok (.sat _) => "sat"
      | .ok (.unsat _ _) => "unsat"
      | .ok (.unknown reason) => "unknown:" ++ reason.toString
      | .error err => "error:" ++ err.toString
    IO.println s!"SOLVER_RESULT {label.getString} status={status} solver_ms={(← IO.monoMsNow)-prepared} smt_prep_ms={prepared-start} bytes={query.utf8ByteSize}"
  catch ex =>
    IO.println s!"SOLVER_FAILURE {label.getString}: {← ex.toMessageData.toString}"
    throw ex


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

set_option maxHeartbeats 0
set_option maxRecDepth 10000

unsat trace [solver_old_4] {
  any 4 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "Peterson_old_4"
  sorry

unsat trace [solver_early_4] {
  any 4 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  veil_intros
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "Peterson_early_4"
  sorry

unsat trace [solver_old_8] {
  any 8 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "Peterson_old_8"
  sorry

unsat trace [solver_early_8] {
  any 8 actions
  assert (∃ p, pc p critical ∨ pc p release)
} by
  veil_intros
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "Peterson_early_8"
  sorry

end Peterson
