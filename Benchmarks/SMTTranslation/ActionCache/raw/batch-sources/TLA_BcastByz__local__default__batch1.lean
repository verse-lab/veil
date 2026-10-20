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

open Std
/-
src : https://github.com/tlaplus/Examples/blob/master/specifications/bcastByz/bcastByz.tla
This file specifies the Byzantine broadcast protocol in Veil, which is a
TLA+ encoding of a parameterized model of the broadcast distributed algorithm
with Byzantine faults.

This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

[1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
simple fault-tolerant algorithms. Distributed Computing 1987,
Volume 2, Issue 2, pp 80-94

The protocol works as follows:
- There are N processes, of which F can be faulty (Byzantine)
- There are T >= F possible faulty processes
- The constraint is N > 3*T
- Processes can be in states: V0 (no INIT), V1 (received INIT), SE (sent ECHO), AC (accepted)
- Correct processes send ECHO messages based on certain conditions
- A correct process accepts when it receives enough ECHO messages

-/
veil module BcastByz

type process
type procSet
instantiate pset : TSet process procSet
-- instantiate thread : Fintype process

enum PCState = { V0, V1, SE, AC }

-- N: total number of processes
-- T: upper bound on Byzantine processes
-- F: actual number of faulty processes
immutable individual N : Nat
immutable individual T : Nat
immutable individual F : Nat
-- immutable individual Proc : procSet

instantiate processEnumerable : Veil.Enumeration process

-- State variables

-- M == { "ECHO" }
-- immutable individual M : process
-- (* ByzMsgs == { <<p, "ECHO">> : p \in Faulty }: quite complicated to write a TLAPS proof
--    for the cardinality of the expression { e : x \in S}
--  *)

-- individual Corr : Finset process    -- correct processes
individual Corr : procSet
individual Faulty : procSet             -- faulty processes
function pc (p : process) : PCState  -- control state of each process
-- relation pointer (ph : phase)             -- current phase of the protocol

-- In TLA+: sent \subseteq Proc \times M
-- Since all messages are <<p, "ECHO">>, we only need to track which processes have sent
-- sent is the set of processes that have sent messages
-- relation sent (p : process)
individual sent : procSet
function rcvd (receiver : process) : procSet

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

-- Ghost definitions for readability
ghost relation isCorrect (p : process) := pset.contains p Corr
ghost relation isFaulty (p : process) := pset.contains p Faulty
-- Initial state

-- Init ==
--   /\ sent = {}                          (* No messages sent initially *)
--   /\ pc \in [ Proc -> {"V0", "V1"} ]    (* Some processes received INIT messages, some didn't *)
--   /\ rcvd = [ i \in Proc |-> {} ]       (* No messages received initially *)
--   /\ Corr \in SUBSET Proc
--   /\ Cardinality(Corr) = N - F          (* N - F processes are correct, but their identities are unknown*)
--   /\ Faulty = Proc \ Corr               (* The rest (F) are faulty*)
after_init {
  sent := pset.empty
  rcvd P := pset.empty
  let V1Set ← pick procSet
  pc P := if pset.contains P V1Set then V1 else V0
  let corrSet :| pset.count corrSet = N - F
  Corr := corrSet
  Faulty := pset.diff (pset.ofList processEnumerable.allValues) Corr
}

-- ByzMsgs == Faulty \X M

-- Receive(self, includeByz) ==
--   \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
--     rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]
-- ReceiveFromCorrectSender(self) == Receive(self, FALSE)
-- ReceiveFromAnySender(self) == Receive(self, TRUE)
procedure Receive (self : process) (includeByz : Bool) {
  let superSet := if includeByz then pset.union sent Faulty else sent
  let newMessages :| pset.isSubset newMessages superSet
  rcvd self := pset.union (rcvd self) newMessages
}

-- NOTE: `ReceiveFromCorrectSender` is not used in the `Step` part

procedure ReceiveFromAnySender (self : process) {
  Receive self true
}

/- This action is used to model the behavior of a process
doing nothing (stuttering) in TLA+, which corresponding to Line 160:
  `\/ UNCHANGED vars (* add a self-loop for terminating computations *)`
in bcastByz.tla.
With this action, we can not only obtain the same
number of `distinct states` as TLA+ verision, but `total states` as well.-/
action Stutter {
  pure ()
}

-- UponV1(self) ==
--   /\ pc[self] = "V1"
--   /\ pc' = [pc EXCEPT ![self] = "SE"]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponV1 (self : process) {
  require isCorrect self
  require pc self = V1
  ReceiveFromAnySender self
  pc self := SE
  sent := pset.insert self sent
}

-- UponNonFaulty(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - 2*T
--   /\ Cardinality(rcvd'[self]) < N - T
--   /\ pc' = [ pc EXCEPT ![self] = "SE" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponNonFaulty (self : process) {
  require isCorrect self
  require pc self ∈ [V0, V1]
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - 2 * T
  assume pset.count (rcvd self) < N - T
  pc self := SE
  sent := pset.insert self sent
}

-- UponAcceptNotSentBefore(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [ pc EXCEPT ![self] = "AC" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponAcceptNotSentBefore (self : process) {
  require isCorrect self
  require pc self ∈ [V0, V1]
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - T
  pc self := AC
  sent := pset.insert self sent
}

-- UponAcceptSentBefore(self) ==
--   /\ pc[self] = "SE"
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [pc EXCEPT ![self] = "AC"]
--   /\ sent' = sent
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponAcceptorSentBefore (self : process) {
  require isCorrect self
  require pc self = SE
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - T
  pc self := AC
}

-- Step(self) ==
--   /\ ReceiveFromAnySender(self)
--   /\ \/ UponV1(self)
--      \/ UponNonFaulty(self)
--      \/ UponAcceptNotSentBefore(self)
--      \/ UponAcceptSentBefore(self)

-- Parameter constraints from TLA+ specification
-- TypeOK == /\ N \in Nat \ {0}
--           /\ T \in Nat
--           /\ F \in Nat
--           /\ N > 3 * T
--           /\ T >= F
-- procedure ByzMsgs {
--   return pset.remove M Faulty
-- }

invariant [Corr_cup_faulty_eq_proc] pset.union Corr Faulty == (pset.ofList processEnumerable.allValues)
invariant [card_corr] pset.count Corr ≥ N - T
invariant [card_faulty] pset.count Faulty ≤ T


#gen_spec
run_cmd discard <| _root_.Veil.Verifier.waitFilteredSync _root_.Veil.Verifier.isDoesNotThrow

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-action-cache/results/batch-events/TLA_BcastByz__local__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ p, isCorrect p ∧ pc p = AC)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_BcastByz__d1__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_BcastByz__d1__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any 2 actions
  assert (∃ p, isCorrect p ∧ pc p = AC)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_BcastByz__d2__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_BcastByz__d2__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 4 actions
  assert (∃ p, isCorrect p ∧ pc p = AC)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_BcastByz__d4__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_BcastByz__d4__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 8 actions
  assert (∃ p, isCorrect p ∧ pc p = AC)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_BcastByz__d8__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_BcastByz__d8__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 16 actions
  assert (∃ p, isCorrect p ∧ pc p = AC)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_BcastByz__d16__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_BcastByz__d16__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 32 actions
  assert (∃ p, isCorrect p ∧ pc p = AC)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_BcastByz__d32__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_BcastByz__d32__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_BcastByz__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end BcastByz
