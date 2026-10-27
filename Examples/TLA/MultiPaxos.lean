module

public import Veil

-- source: https://github.com/sachand/HistVar/blob/692e1e5b9c5e89f649af44613b62e557f6b569af/Multi-Paxos/MultiPaxosUs.tla

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

instantiate mem : Membership acceptor quorum

individual sent : MsgSet

-- Slots == 0..MaxSlot (provided as a list for iteration in FreeSlots)
-- immutable individual SlotsUNIV : List slot
instantiate slotEnumerable : Veil.Enumeration slot

set_option veil.deferVCGeneration true

#gen_state

assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : acceptor), r ∈ q1 ∧ r ∈ q2

after_init {
  sent := msgSet.empty
}

procedure Send (m : MsgSet) {
  sent := msgSet.union m sent
}

-- TODO need singleton

action Phase1a (p : proposer) {
  let b ← pick (BallotTy maxBallot)
  Send (msgSet.ofList [(.phase1a p b)])
}

ghost function voteds (a : acceptor) : VotedSet :=
  msgSet.filterMap sent fun m =>
    match m with
    | .phase2b src bal slot val => if src = a then some { bal := bal, slot := slot, val := val } else none
    | _ => none

ghost function PartialBmax (T : VotedSet) : VotedSet :=
  voteSet.filter T fun t =>
    decide <|
      ∀ t1 : { t1 // t1 ∈ T }, t1.val.slot = t.slot → t1.val.bal ≤ t.bal

-- Ghost relation: all previous 1b/2b messages from acceptor a have ballot < b
ghost relation allPrevBallotsLower (a : acceptor) (b : BallotTy maxBallot) :=
  ∀ m : { m // m ∈ sent }, (match m.val with
    | .phase1b src bal _ => decide $ src = a → bal < b
    | .phase2b src bal _ _ => decide $ src = a → bal < b
    | _ => true) = true

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

ghost function Bmax (T : VotedSet) : DecreeSet :=
  voteSet.map (PartialBmax T) fun t =>
    { slot := t.slot, val := t.val : Decree slot value }

ghost function FreeSlots (T : VotedSet) : List slot :=
  slotEnumerable.allValues.filter fun s =>
    decide <| ¬ ∃ t : { t // t ∈ T }, t.val.slot = s

ghost function NewProposals (T : VotedSet) : DecreeSet :=
  let freeSlotList := FreeSlots T
  /- TLA+ `CHOOSE` is deterministic. See https://www.learntla.com/core/operators.html.
  "_TLC will always choose the `lowest` value that matches the set_",
  Here simulate `CHOOSE` by picking only the FIRST free slot with default value. -/
  match freeSlotList with
  | [] => decSet.empty
  | s :: _ => decSet.ofList [{ slot := s, val := default }]

ghost function ProposeDecrees (T : VotedSet) : DecreeSet :=
  decSet.union (Bmax T) (NewProposals T)

-- TODO need iterated union

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
ghost relation quorumCovered (Q : quorum) (S : MsgSet) :=
  ∀ a ∈ Q, ∃ m : { m // m ∈ S }, (match m.val with
    | .phase1b src .. => decide $ src = a
    | _ => false) = true

/-
-- Optimization: instead of picking MsgSet (huge), pick AcceptorSet (only 2^n possibilities)
action Phase2a (p : proposer) {
  let b ← pick (BallotTy maxBallot)

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

  require ¬ ∃ msg : { m // m ∈ sent },
    (match msg.val with
      | .phase2a _ bal _ => decide $ bal = b
      | _ => false) = true

  let Q ← pick quorum

  let filtered1b := msgSet.filter sent fun m =>
    match m with
    | .phase1b _ bal _ => decide $ bal = b
    | _ => false
  let S :| msgSet.isSubset S filtered1b

  require quorumCovered Q S

  let proposeDecreesSet := ProposeDecrees (VS S Q)
  Send (msgSet.insert (.phase2a p b proposeDecreesSet) msgSet.empty)
}

-- Ghost relation: all previous 1b/2b messages from acceptor a have ballot ≤ b
ghost relation allPrevBallotsLeq (a : acceptor) (b : BallotTy maxBallot) :=
  ∀ m : { m // m ∈ sent }, (match m.val with
    | .phase1b src bal _ => decide $ src = a → bal ≤ b
    | .phase2b src bal _ _ => decide $ src = a → bal ≤ b
    | _ => true) = true

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

ghost relation VotedForIn (a : acceptor) (b : BallotTy maxBallot) (s : slot) (v : value) :=
  msgSet.contains (.phase2b a b s v) sent

ghost relation ChosenIn (b : BallotTy maxBallot) (s : slot) (v : value) :=
  ∃ (Q : quorum), ∀ a ∈ Q, VotedForIn a b s v

ghost relation Chosen (v : value) (s : slot) :=
  ∃ b, ChosenIn b s v

invariant [consistency]
  ∀ (v1 v2 : value) (s : slot), (Chosen v1 s ∧ Chosen v2 s) → (v1 = v2)

termination false

#gen_spec
#gen_executable

-- The check below uses the instance of the TLC model `Benchmarks/TLA/MultiPaxosUs.cfg`, which
-- TLC runs on `MCMultiPaxosUs.tla`. It is commented out; uncomment it to run it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `slot := Fin 3`: the slots are `0`, `1`, `2` (cfg: `MaxSlot = 2` and `Slots <- MCSlots`,
--   where `MCSlots == 0..MaxSlot`).
-- * `value := Fin 2`: the values are `0`, `1` (cfg: `Values = {v1, v2}`).
-- * `acceptor := Fin 3`: the acceptors are `0`, `1`, `2` (cfg: `Acceptors = {a1, a2, a3}`).
-- * `proposer := Fin 2`: the proposers are `0`, `1` (cfg: `Proposers = {p1, p2}`).
-- * `quorum := MinQuorum (Fin 3)`: the quorums are the sets of two acceptors
--   (cfg: `Quorums = {{a1, a2}, {a1, a3}, {a2, a3}}`).
--   Before searching, `#model_check` checks them against the `assumption [quorum_intersection]`
--   above, which is the spec's `ASSUME QuorumAssumption`.
-- * `maxBallot := 2`: the ballots are `0..2` (cfg: `MaxBallot = 2` and `Ballots <- MCBallots`,
--   where `MCBallots == 0..MaxBallot`).
-- * `VotedSet`, `DecreeSet`, `MsgSet` and `AcceptorSet := OrdList _`: `OrdList` has the `TSet`
--   instances that the `instantiate` lines above require.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields. There are none,
-- hence `{}`.
--
-- The other settings of the cfg:
-- * `NewProposals <- MCNewProposals`: fixes how TLC resolves the `CHOOSE` in `NewProposals`.
--   The ghost function `NewProposals` above fixes its own rule: it proposes the default value
--   for the first free slot.
-- * `INVARIANTS Consistency`: `#model_check` checks every `invariant` of the module, here
--   `consistency`.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `(seenSet := HAMTMapShard)`: the sharded map of visited states uses `HAMTMapShard`.
/- EVAL
#model_check compiled
{
  slot := Fin 3,
  value := Fin 2,
  acceptor := Fin 3,
  proposer := Fin 2,
  quorum := MinQuorum (Fin 3),
  maxBallot := 2,
  VotedSet := OrdList _,
  DecreeSet := OrdList _,
  MsgSet := OrdList _,
  AcceptorSet := OrdList _
} {} (seenSet := HAMTMapShard)
-/

end MultiPaxos
