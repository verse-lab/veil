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
set_option veil.experimental.bmcCache true

-- source: https://github.com/sachand/HistVar/blob/master/Multi-Paxos/MultiPaxosUs.tla
-- ------------------------------- MODULE MultiPaxosUs -------------------------------
-- (***************************************************************************)
-- (* This is a TLA+ specification of the MultiPaxos Consensus algorithm,     *)
-- (* described in                                                            *)
-- (*                                                                         *)
-- (*  The Part-Time Parliament:                                              *)
-- (*  http://research.microsoft.com/en-us/um/people/lamport/pubs/lamport-paxos.pdf *)
-- (*                                                                         *)
-- (* and a TLAPS-checked proof of its correctness. This is an extension of   *)
-- (* the proof of Basic Paxos found in TLAPS examples directory.             *)
-- (***************************************************************************)
-- EXTENDS Integers, FiniteSets

veil module MultiPaxos

-- Ballot type: Fin (maxBallot + 1), encoding TLA+'s Ballots == 0..MaxBallot
-- (Unlike Paxos, MultiPaxos has no "no ballot" sentinel)
abbrev BallotTy (maxBallot : Nat) := Fin (maxBallot + 1)

@[veil_decl]
structure Voted (bl slt vl : Type) where
  bal  : bl
  slot : slt
  val  : vl
deriving instance Veil.Enumeration for Voted

@[veil_decl]
structure Decree (slt vl : Type) where
  slot : slt
  val  : vl
deriving instance Veil.Enumeration for Decree

-- Messages ==
--   [type : {"1a"}, bal : Ballots, from : Proposers]
--   \cup [type : {"1b"}, bal : Ballots, voted : SUBSET [...], from : Acceptors]
--   \cup [type : {"2a"}, bal : Ballots, decrees : SUBSET [...], from : Proposers]
--   \cup [type : {"2b"}, bal : Ballots, slot : Slots, val : Values, from : Acceptors]
@[veil_decl]
inductive Msg (prp ac vl blt slt vcont dcont : Type) where
  | phase1a (src : prp) (bal : blt) : Msg prp ac vl blt slt vcont dcont
  | phase1b (src : ac) (bal : blt) (voted : vcont) : Msg prp ac vl blt slt vcont dcont
  | phase2a (src : prp) (bal : blt) (decrees : dcont) : Msg prp ac vl blt slt vcont dcont
  | phase2b (src : ac) (bal : blt) (slot : slt) (val : vl) : Msg prp ac vl blt slt vcont dcont
deriving instance Veil.Enumeration for Msg

abbrev Msg.ballot (m : Msg prp ac vl blt slt vcont dcont) : blt :=
  match m with
  | .phase1a _ bal => bal
  | .phase1b _ bal _ => bal
  | .phase2a _ bal _ => bal
  | .phase2b _ bal _ _ => bal

abbrev MultiPaxosMsg (prp ac vl : Type) (maxBallot : Nat) (slt vcont dcont : Type) :=
  Msg prp ac vl (BallotTy maxBallot) slt vcont dcont

abbrev MultiPaxosVoted (maxBallot : Nat) (slot value : Type) :=
  Voted (BallotTy maxBallot) slot value

-- CONSTANTS Acceptors, Values, Quorums, Proposers, MaxBallot, MaxSlot
type acceptor
type proposer
type value
type quorum
type slot

param maxBallot : Nat

type VotedSet
type DecreeSet
type MsgSet
type AcceptorSet

instantiate voteSet : TSet (MultiPaxosVoted maxBallot slot value) VotedSet
instantiate decSet : TSet (Decree slot value) DecreeSet
instantiate msgSet : TSet (MultiPaxosMsg proposer acceptor value maxBallot slot VotedSet DecreeSet) MsgSet
instantiate acSet : TSet acceptor AcceptorSet

-- ASSUME QuorumAssumption
instantiate mem : Membership acceptor quorum

-- VARIABLES sent
individual sent : MsgSet

-- Slots == 0..MaxSlot (provided as a list for iteration in FreeSlots)
-- immutable individual SlotsUNIV : List slot
instantiate slotEnumerable : Veil.Enumeration slot

#gen_state

assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : acceptor), r ∈ q1 ∧ r ∈ q2

-- Init == /\ sent = {}
after_init {
  sent := msgSet.empty
}

-- Send(m) == sent' = sent \cup m
procedure Send (m : MsgSet) {
  sent := msgSet.union m sent
}

-- (***************************************************************************)
-- (* Phase 1a: Executed by a proposer, it selects a ballot number on which   *)
-- (* Phase 1a has never been initiated. This number is sent to any set of    *)
-- (* acceptors which contains at least one quorum from Quorums. Trivially it *)
-- (* can be broadcasted to all Acceptors. For safety, any subset of          *)
-- (* Acceptors would suffice. For liveness, a subset containing at least one *)
-- (* Quorum is needed.                                                       *)
-- (***************************************************************************)

-- TODO need singleton

-- Phase1a(p) == \E b \in Ballots: Send({[type |-> "1a", from |-> p, bal |-> b]})
action Phase1a (p : proposer) {
  let b ← pick (BallotTy maxBallot)
  Send (msgSet.ofList [(.phase1a p b)])
}

-- (***************************************************************************)
-- (* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
-- (* than that of any 1a message to which it has already responded, then it  *)
-- (* responds to the request with a promise not to accept any more proposals *)
-- (* for ballots numbered less than b; otherwise it sends a preempt to the   *)
-- (* proposer telling the greater ballot.                                    *)
-- (* In case of a 1b reply, the acceptor writes a mapping in S -> B \times V *)
-- (* This This mapping reveals for each slot, the value that the acceptor    *)
-- (* most recently (i.e., highest ballot) voted on, if any.                  *)
-- (***************************************************************************)

-- voteds(a) == {[bal |-> m.bal, slot |-> m.slot, val |-> m.val]:
--               m \in {m \in sent: m.type = "2b" /\ m.from = a}}
ghost function voteds (a : acceptor) : VotedSet :=
  msgSet.filterMap sent fun m =>
    match m with
    | .phase2b src bal slot val => if src = a then some { bal := bal, slot := slot, val := val } else none
    | _ => none

-- PartialBmax(T) ==
--   {t \in T : \A t1 \in T : t1.slot = t.slot => t1.bal =< t.bal}
ghost function PartialBmax (T : VotedSet) : VotedSet :=
  voteSet.filter T fun t =>
    decide <|
      ∀ t1 : { t1 // t1 ∈ T }, t1.val.slot = t.slot → t1.val.bal ≤ t.bal

-- Ghost relation: all previous 1b/2b messages from acceptor a have ballot < b
-- Encodes: \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: b > m2.bal
ghost relation allPrevBallotsLower (a : acceptor) (b : BallotTy maxBallot) :=
  ∀ m : { m // m ∈ sent }, (match m.val with
    | .phase1b src bal _ => decide $ src = a → bal < b
    | .phase2b src bal _ _ => decide $ src = a → bal < b
    | _ => true) = true

-- Phase1b(a) == \E m \in sent:
--   /\ m.type = "1a"
--   /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal > m2.bal
--   /\ Send({[type |-> "1b", from |-> a, bal |-> m.bal, voted |-> PartialBmax(voteds(a))]})
action Phase1b (a : acceptor) {
  let m : { m // m ∈ sent } :| (match m.val with
    | .phase1a _ _ => true
    | _ => false) = true
  let b := m.val.ballot
  require allPrevBallotsLower a b
  let votedSet := voteds a
  let partialBmaxSet := PartialBmax votedSet
  Send (msgSet.ofList [(.phase1b a b partialBmaxSet)])
}

-- (***************************************************************************)
-- (* Phase 2a: If the proposer receives a response to its 1b message (for    *)
-- (* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
-- (* acceptors for a proposal in ballot b. Per slot received in the replies, *)
-- (* the proposer finds out the value most recently (i.e., highest ballot)   *)
-- (* voted by the acceptors in the received set. Thus a mapping in S -> V    *)
-- (* is created. This mapping along with the ballot that passed Phase 1a is  *)
-- (* propogated to again, any subset of Acceptors - Hopefully to one         *)
-- (* containing at least one Quorum.                                         *)
-- (* Bmax            creates the desired mapping from received replies.      *)
-- (* NewProposals    instructs how new slots are entered in the system.      *)
-- (***************************************************************************)

-- Bmax(T) ==
--   {[slot |-> t.slot, val |-> t.val] : t \in PartialBmax(T)}
ghost function Bmax (T : VotedSet) : DecreeSet :=
  voteSet.map (PartialBmax T) fun t =>
    { slot := t.slot, val := t.val : Decree slot value }

-- FreeSlots(T) ==
--   {s \in Slots : ~ \E t \in T : t.slot = s}
ghost function FreeSlots (T : VotedSet) : List slot :=
  slotEnumerable.allValues.filter fun s =>
    decide <| ¬ ∃ t : { t // t ∈ T }, t.val.slot = s

-- NewProposals(T) ==
--   (CHOOSE D \in SUBSET [slot : FreeSlots(T), val : Values] \ {}:
--     \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2)
ghost function NewProposals (T : VotedSet) : DecreeSet :=
  let freeSlotList := FreeSlots T
  /- TLA+ `CHOOSE` is deterministic. See https://www.learntla.com/core/operators.html.
  "_TLC will always choose the `lowest` value that matches the set_",
  Here simulate `CHOOSE` by picking only the FIRST free slot with default value. -/
  match freeSlotList with
  | [] => decSet.empty
  | s :: _ => decSet.ofList [{ slot := s, val := default }]

-- ProposeDecrees(T) ==
--   Bmax(T) \cup NewProposals(T)
ghost function ProposeDecrees (T : VotedSet) : DecreeSet :=
  decSet.union (Bmax T) (NewProposals T)

-- TODO need iterated union

-- VS(S, Q) == UNION {m.voted: m \in {m \in S: m.from \in Q}}
ghost function VS (S : MsgSet) (Q : quorum) : VotedSet :=
  -- NOTE: Here we implicitly require that S only contains `1b` messages,
  -- due to some typing issue
  let sub := msgSet.filter S fun m =>
    match m with
    | .phase1b src _ _ => decide (src ∈ Q)
    | _ => false
  msgSet.toList sub |>.foldl (init := voteSet.empty) fun acc m =>
    match m with
    | .phase1b _ _ voted => voteSet.union acc voted
    | _ => acc

-- Ghost relation: quorum Q is covered by 1b messages in S
-- Encodes: \A a \in Q: \E m \in S: m.from = a
ghost relation quorumCovered (Q : quorum) (S : MsgSet) :=
  ∀ a ∈ Q, ∃ m : { m // m ∈ S }, (match m.val with
    | .phase1b src .. => decide $ src = a
    | _ => false) = true

-- Phase2a(p) == \E b \in Ballots:
--   /\ ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
--   /\ \E Q \in Quorums, S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}:
--        /\ \A a \in Q: \E m \in S: m.from = a
--        /\ Send({[type |-> "2a", from |-> p, bal |-> b, decrees |-> ProposeDecrees(VS(S, Q))]})

/-
-- Optimization: instead of picking MsgSet (huge), pick AcceptorSet (only 2^n possibilities)
action Phase2a (p : proposer) {
  let b ← pick (BallotTy maxBallot)

  -- ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
  require ¬ ∃ msg : { m // m ∈ sent },
    (match msg.val with
      | .phase2a _ bal _ => decide $ bal = b
      | _ => false) = true

  let Q ← pick quorum

  /- Instead of picking S from the set of all subsets of messages,
    we pick a subset of acceptors, and construct S by filtering messages from those
    acceptors. As we only care about condition `m.from = a`.
    This reduces the non-deterministic choices to 2^|acceptors|.  -/
  let selectedAcceptors ← pick AcceptorSet
  let S := msgSet.filter sent (fun m =>
    match m with
    | .phase1b src bal _ => bal == b && acSet.contains src selectedAcceptors
    | _ => false)

  require quorumCovered Q S

  let proposeDecreesSet := ProposeDecrees (VS S Q)
  Send (msgSet.ofList [(.phase2a p b proposeDecreesSet)])
}
-/

-- Authentic translation: pick S directly from SUBSET of filtered 1b messages
action Phase2a (p : proposer) {
  let b ← pick (BallotTy maxBallot)

  -- ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
  require ¬ ∃ msg : { m // m ∈ sent },
    (match msg.val with
      | .phase2a _ bal _ => decide $ bal = b
      | _ => false) = true

  let Q ← pick quorum

  -- S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}
  let filtered1b := msgSet.filter sent fun m =>
    match m with
    | .phase1b _ bal _ => decide $ bal = b
    | _ => false
  let S :| msgSet.isSubset S filtered1b

  -- \A a \in Q: \E m \in S: m.from = a
  require quorumCovered Q S

  let proposeDecreesSet := ProposeDecrees (VS S Q)
  Send (msgSet.insert (.phase2a p b proposeDecreesSet) msgSet.empty)
}

-- (***************************************************************************)
-- (* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
-- (* the highest that it has seen, it votes for all the message's values     *)
-- (* in ballot b.                                                            *)
-- (***************************************************************************)

-- Ghost relation: all previous 1b/2b messages from acceptor a have ballot ≤ b
-- Encodes: \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: b >= m2.bal
ghost relation allPrevBallotsLeq (a : acceptor) (b : BallotTy maxBallot) :=
  ∀ m : { m // m ∈ sent }, (match m.val with
    | .phase1b src bal _ => decide $ src = a → bal ≤ b
    | .phase2b src bal _ _ => decide $ src = a → bal ≤ b
    | _ => true) = true

-- Phase2b(a) == \E m \in sent:
--   /\ m.type = "2a"
--   /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal >= m2.bal
--   /\ Send({[type |-> "2b", from |-> a, bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees})
action Phase2b (a : acceptor) {
  let m : { m // m ∈ sent } :| (match m.val with
    | .phase2a .. => true
    | _ => false) = true
  let b := m.val.ballot
  require allPrevBallotsLeq a b
  let decrees := match m.val with
    | .phase2a _ _ d => d
    | _ => default  -- dead branch
  let replyMsgSet := decSet.map decrees fun d =>
    Msg.phase2b a b d.slot d.val
  Send replyMsgSet
}

-- VotedForIn(a, b, s, v) ==
--   \E m \in sent : /\ m.type = "2b" /\ m.bal = b /\ m.slot = s /\ m.val = v /\ m.from = a
ghost relation VotedForIn (a : acceptor) (b : BallotTy maxBallot) (s : slot) (v : value) :=
  msgSet.contains (.phase2b a b s v) sent

-- ChosenIn(b, s, v) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, b, s, v)
ghost relation ChosenIn (b : BallotTy maxBallot) (s : slot) (v : value) :=
  ∃ (Q : quorum), ∀ a ∈ Q, VotedForIn a b s v

-- Chosen(v, s) == \E b \in Ballots : ChosenIn(b, s, v)
ghost relation Chosen (v : value) (s : slot) :=
  ∃ b, ChosenIn b s v

-- Consistency == \A v1, v2 \in Values, s \in Slots : Chosen(v1, s) /\ Chosen(v2, s) => (v1 = v2)
invariant [consistency]
  ∀ (v1 v2 : value) (s : slot), (Chosen v1 s ∧ Chosen v2 s) → (v1 = v2)


#gen_spec
run_cmd discard <| _root_.Veil.Verifier.waitFilteredSync _root_.Veil.Verifier.isDoesNotThrow

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-action-cache/results/batch-events/TLA_MultiPaxos__cached__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d1__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ v1 v2 s, Chosen v1 s ∧ Chosen v2 s ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d1__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_MultiPaxos__d1__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d1__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d2__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any 2 actions
  assert (∃ v1 v2 s, Chosen v1 s ∧ Chosen v2 s ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d2__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_MultiPaxos__d2__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d2__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d4__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 4 actions
  assert (∃ v1 v2 s, Chosen v1 s ∧ Chosen v2 s ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d4__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_MultiPaxos__d4__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d4__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d8__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 8 actions
  assert (∃ v1 v2 s, Chosen v1 s ∧ Chosen v2 s ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d8__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_MultiPaxos__d8__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d8__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d16__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 16 actions
  assert (∃ v1 v2 s, Chosen v1 s ∧ Chosen v2 s ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d16__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_MultiPaxos__d16__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d16__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d32__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 32 actions
  assert (∃ v1 v2 s, Chosen v1 s ∧ Chosen v2 s ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d32__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_MultiPaxos__d32__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_MultiPaxos__d32__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end MultiPaxos
