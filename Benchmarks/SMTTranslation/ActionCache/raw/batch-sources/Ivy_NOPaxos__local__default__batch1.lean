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

/-
  This is a simplified version of the NOPaxos protocol, without view
  changes. As such, the leader is modelled as fixed.
-/
veil module NOPaxos

type replica -- replica ID
enum replica_state = { st_normal, st_gap_commit } -- we don't model view changes
type seq_t
type value
type quorum

instantiate seq : TotalOrderWithZero seq_t

immutable individual one : seq_t
immutable individual no_op : value
-- We don't model view changes, so the leader is fixed
immutable individual leader : replica

immutable relation member (R : replica) (Q : quorum)

-- Sequencer, indicating the _next_ message number to be sequenced
-- NOTE: We don't model view changes (which can happen due to session termination),
-- so we only have one sequencer.
individual s_seq_msg_num : seq_t

-- Replica
relation r_log_len (r : replica) (i : seq_t)
relation r_log (r : replica) (i : seq_t) (v : value)
relation r_sess_msg_num (r : replica) (i : seq_t)   -- the expected _next_ message number
relation r_gap_commit_reps (r : replica) (p : replica)
relation r_current_gap_slot (r : replica) (i : seq_t)
relation r_replica_status (r : replica) (s : replica_state)

-- Network
relation m_client_request (v : value)
relation m_marked_client_request  (dest : replica) (v : value) (sess_msg_num : seq_t)
relation m_request_reply (sender : replica) (request : value) (log_slot_num : seq_t)
relation m_slot_lookup (dest : replica) (sender : replica) (sess_msg_num : seq_t)
relation m_gap_commit (dest : replica) (slot_num : seq_t)
relation m_gap_commit_rep (dest : replica) (sender : replica) (slot_num : seq_t)

-- Ghost state
relation gh_r_received_sequenced_client_request (r : replica) (s : seq_t)
relation gh_r_received_drop_notification (r : replica) (s : seq_t)
relation gh_committed (s : seq_t) (v : value)

#gen_state

theory ghost relation lt (x y : seq_t) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : seq_t) := (lt x y ∧ ∀ z, lt x z → seq.le y z)

assumption [zero_one] next seq.zero one
assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : replica), member r q1 ∧ member r q2

after_init {
  -- Arrays in TLA+ are 1-indexed, and we follow the same convention here
  s_seq_msg_num := one;

  r_log_len R I := I == seq.zero
  r_log R I V := false
  r_sess_msg_num R I := I == one
  r_gap_commit_reps R P := false
  r_current_gap_slot R I := I == seq.zero
  r_replica_status R S := S == st_normal

  m_client_request V := false
  m_marked_client_request D V SMN := false
  m_request_reply S V LSN := false
  m_slot_lookup D S SMN := false
  m_gap_commit D SN := false
  m_gap_commit_rep D S SN := false

  gh_r_received_sequenced_client_request R S := false
  gh_r_received_drop_notification R S := false
  gh_committed S V := false
}

procedure succ (n : seq_t) {
  let k :| next n k
  return k
}

procedure replace_item (r : replica) (i : seq_t) (v : value) {
  let len :| r_log_len r len
  let next_len ← succ len
  if seq.le i next_len then
    if i = next_len then
      r_log_len r I := I == i
    r_log r i V := V == v
}

action client_sends_request (v : value) {
  require v ≠ no_op
  m_client_request v := true
}

-- Sequencer handles the client request
action handle_client_request (m_value : value) {
  require m_client_request m_value
  let slot := s_seq_msg_num
  m_marked_client_request R m_value slot := true
  let next_slot ← succ slot
  s_seq_msg_num := next_slot
}

procedure append_to_log (r : replica) (v : value) {
  let len :| r_log_len r len
  -- TLA arrays are 1-indexed, so we replicate this here
  let next_len ← succ len
  r_log r next_len v := true
  r_log_len r I := I == next_len
  return next_len
}

procedure increase_session_number (r : replica) {
  let smn :| r_sess_msg_num r smn
  let next_smn ← succ smn
  r_sess_msg_num r I := I == next_smn
  return next_smn
}

-- Normal case of `HandleMarkedClientRequest`
action handle_marked_client_request_normal (r : replica) (m_value : value) (m_sess_msg_num : seq_t) {
  require m_marked_client_request r m_value m_sess_msg_num
  require r_replica_status r st_normal
  let smn :| r_sess_msg_num r smn
  require m_sess_msg_num = smn
  gh_r_received_sequenced_client_request r m_sess_msg_num := true
  let _new_smn ← increase_session_number r
  let new_len ← append_to_log r m_value
  m_request_reply r m_value new_len := true
}


procedure send_gap_commit (r : replica) {
  require r = leader
  require r_replica_status r st_normal
  let len :| r_log_len r len
  let slot ← succ len
  r_replica_status r S := S == st_gap_commit
  r_gap_commit_reps r P := false
  r_current_gap_slot r I := I == slot
  m_gap_commit R slot := true
}

-- Drop notification case of `HandleMarkedClientRequest`
action handle_marked_client_drop_notification (r : replica) (m_value : value) (m_sess_msg_num : seq_t) {
  require m_marked_client_request r m_value m_sess_msg_num
  require r_replica_status r st_normal
  let smn :| r_sess_msg_num r smn
  -- NOTE: this is the condition in the TLA+ spec, but it means that
  -- a drop notification cannot be sent for the first session number,
  -- which seems incorrect.
  require lt smn m_sess_msg_num
  gh_r_received_drop_notification r m_sess_msg_num := true
  if r = leader then
    send_gap_commit r
  else
    m_slot_lookup leader r smn := true
}

action handle_slot_lookup (r : replica) (m_sender : replica) (m_sess_msg_num : seq_t) {
  require m_slot_lookup r m_sender m_sess_msg_num
  require r_replica_status r st_normal
  require r = leader
  let len :| r_log_len r len
  let smn :| r_sess_msg_num r smn
  -- Note: in TLA+ the slot is computed as
  -- `logSlotNum == Len(vLog[r]) + 1 - (vSessMsgNum[r] - m.sessMsgNum)`
  -- which calculates the offset from the tail of the log;
  -- however, with no view changes, this is equivalent to simply taking
  -- the index of the incoming m.sessMsgNum
  -- (i.e., with no view changes, we should have `vSessMsgNum[r]` = `Len(vLog[r]) + 1`)
  let slot := m_sess_msg_num
  if seq.le slot len then
    -- NOTE: cannot make this into a pick-such-that because it might not exist
    if v :| r_log r slot v then
      m_marked_client_request m_sender v m_sess_msg_num := true
    else
      -- Nothing to undo
      pure ()
  if slot = (← succ len) then
    send_gap_commit r
}

-- Replica r (or the leader) receives GapCommit
action handle_gap_commit (r : replica) (m_slot_num : seq_t) {
  require m_gap_commit r m_slot_num
  let len :| r_log_len r len
  -- NOTE: this condition ensures that the skipping operation (the `if` block
  -- below) is meaningful, or intuitively "neither too early nor too late"
  require seq.le m_slot_num len ∨ next len m_slot_num
  let smn :| r_sess_msg_num r smn
  replace_item r m_slot_num no_op
  if lt len m_slot_num then
    let  _new_smn ← increase_session_number r
  m_gap_commit_rep leader r m_slot_num := true
  let st :| r_replica_status r st
  m_request_reply r no_op m_slot_num := true
}

action handle_gap_commit_rep (r : replica) (m_sender : replica) (m_slot_num : seq_t) {
  require m_gap_commit_rep r m_sender m_slot_num
  require r_replica_status r st_gap_commit
  require r = leader
  require r_current_gap_slot r m_slot_num
  r_gap_commit_reps r m_sender := true
  if (r_gap_commit_reps r r) ∧ (∃ (q:quorum), ∀ (p:replica),
    member p q → r_gap_commit_reps r p) then
    r_replica_status r S := S == st_normal
}

action client_commit (s : seq_t) (v : value) {
  require ∃ (q:quorum), ∀ (p:replica), member p q → m_request_reply p v s
  require m_request_reply leader v s
  gh_committed s v := true
}

-- invariants for functions (implemented as partial functions)
invariant [ll_coherence] (r_log_len R I1 ∧ r_log_len R I2) → I1 = I2
invariant [log_coherence] (r_log R I V1 ∧ r_log R I V2) → V1 = V2
invariant [smn_coherence] (r_sess_msg_num R I1 ∧ r_sess_msg_num R I2) → I1 = I2
invariant [cgs_coherence] (r_current_gap_slot R I1 ∧ r_current_gap_slot R I2) → I1 = I2
invariant [status_coherence] (r_replica_status R S1 ∧ r_replica_status R S2) → S1 = S2

-- sanity checks
invariant [leader_status_either] r_replica_status leader st_normal ∨ r_replica_status leader st_gap_commit
invariant [only_leader_can_gap_status] r_replica_status R st_gap_commit → R = leader
invariant [m_gap_commit_rep_to_leader_only] m_gap_commit_rep R P S → R = leader
invariant [client_no_op] ¬ m_client_request no_op
invariant [log_valid_1] (r_log R I V ∧ r_log_len R L) → seq.le I L

-- a useful relation
invariant [valid_sess_msg_num] (r_log_len R I ∧ r_sess_msg_num R J) → next I J
invariant [log_smn] (r_sess_msg_num R I ∧ seq.le I J) → ¬ r_log R J V   -- weaker than `valid_sess_msg_num`

safety [consistency] gh_committed S V1 ∧ gh_committed S V2 → V1 = V2

/-  To prove consistency, it suffices to show that the leader never rolls back
    by sending two different replies for the same request. -/
invariant [gh_committed_cause] gh_committed S V → m_request_reply leader V S
invariant [leader_never_rolls_back] (m_request_reply leader V1 S ∧ m_request_reply leader V2 S) → V1 = V2

/-  This can be reduced to showing that the log of the leader never gets overwritten. -/
invariant [leader_reply_matches_log] (m_request_reply leader V I) → r_log leader I V

/-  The only possibility that the leader's log might be overwritten is
    that `replace_item` happens inside `handle_gap_commit`. For this, we show that
    this replacement does not change the protocol (i.e., it is just changing
    an existing `no_op` with `no_op`). -/
invariant [lead_gap_commits] (r_log_len leader I ∧ seq.le J I ∧ m_gap_commit R J) → r_log leader J no_op
invariant [log_smn_gap] (m_gap_commit R S ∧ r_sess_msg_num leader I) → seq.le S I
invariant [log_smn_gap_normal] (m_gap_commit R S ∧ r_log_len leader I ∧ r_replica_status leader st_normal) → seq.le S I

-- connecting `m_gap_commit`, `m_gap_commit_rep`, `r_current_gap_slot`, `m_gap_commit_rep` together
invariant [r_gap_commit_reps_source] (r_replica_status leader st_gap_commit ∧ r_current_gap_slot leader I ∧ r_gap_commit_reps leader P) → m_gap_commit_rep leader P I
invariant [m_gap_commit_rep_len] (m_gap_commit_rep R P S ∧ r_log_len P I) → seq.le S I
invariant [m_gap_commit_slot] (r_replica_status leader st_gap_commit ∧ m_gap_commit R S ∧ r_current_gap_slot leader I) → seq.le S I

set_option maxHeartbeats 10000000

#gen_spec
run_cmd discard <| _root_.Veil.Verifier.waitFilteredSync _root_.Veil.Verifier.isDoesNotThrow

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-action-cache/results/batch-events/Ivy_NOPaxos__local__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ s v1 v2, gh_committed s v1 ∧ gh_committed s v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d1__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d1__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any 2 actions
  assert (∃ s v1 v2, gh_committed s v1 ∧ gh_committed s v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d2__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d2__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 4 actions
  assert (∃ s v1 v2, gh_committed s v1 ∧ gh_committed s v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d4__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d4__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 8 actions
  assert (∃ s v1 v2, gh_committed s v1 ∧ gh_committed s v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d8__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d8__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 16 actions
  assert (∃ s v1 v2, gh_committed s v1 ∧ gh_committed s v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d16__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d16__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 32 actions
  assert (∃ s v1 v2, gh_committed s v1 ∧ gh_committed s v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d32__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d32__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end NOPaxos
