import Veil
import Mathlib.Tactic.ProxyType

open Lean

open Std
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
-- EXTENDS Integers, TLAPS

veil module MultiPaxosUs
-- CONSTANTS Acceptors, Values, Quorums, Proposers
-- type Ballots
type ballot
-- type Slots
type slot
-- type Values
type value
-- type Acceptors
-- Proposers
type acceptor
type quorum



structure Voted (α β γ : Type) where
  bal  : α
  slot : β
  val  : γ
deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Hashable, Ord, Repr

section VariousByEquiv

variable {α : Type u} {β : Type v} [Ord α] [Ord β] (equiv : α ≃ β)
  (hmorph : ∀ (a1 a2 : α), compare a1 a2 = compare (equiv a1) (equiv a2))

include hmorph

def Std.TransOrd.by_equiv [inst : Std.TransOrd α] : Std.TransOrd β where
  eq_swap := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.eq_swap
  isLE_trans := by
    intro b1 b2 b3
    rw [← equiv.right_inv b1, ← equiv.right_inv b2, ← equiv.right_inv b3] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.isLE_trans

def Std.LawfulEqOrd.by_equiv [inst : Std.LawfulEqOrd α] : Std.LawfulEqOrd β where
  compare_self := by
    intro b ; specialize hmorph (equiv.symm b) (equiv.symm b) ; grind
  eq_of_compare := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    simp

end VariousByEquiv

namespace Voted

def votedEquiv : Voted α β γ ≃ (α × β × γ) where
  toFun v := (v.bal, v.slot, v.val)
  invFun := fun (a, b, c) => { bal := a, slot := b, val := c }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl


theorem voted_compare_hmorph
  [Ord α] [Ord β] [Ord γ]
  (v1 v2 : Voted α β γ) :
  compare v1 v2 = compare (votedEquiv v1) (votedEquiv v2) := by
  simp [Ord.compare, votedEquiv, instOrdVoted.ord]

instance instTransOrdForVoted
[Ord α] [Ord β] [Ord γ]
[Std.TransOrd α]
[Std.TransOrd β]
[Std.TransOrd γ]
: Std.TransOrd (Voted α β γ) :=
  @Std.TransOrd.by_equiv (α × β × γ) (Voted α β γ) _ _ votedEquiv.symm
    (fun a1 a2 => (voted_compare_hmorph (votedEquiv.symm a1) (votedEquiv.symm a2)).symm)
    inferInstance

instance instLawfulEqOrdForVoted
[Ord α] [Ord β] [Ord γ]
[Std.LawfulEqOrd α]
[Std.LawfulEqOrd β]
[Std.LawfulEqOrd γ]
: Std.LawfulEqOrd (Voted α β γ) :=
  @Std.LawfulEqOrd.by_equiv (α × β × γ) (Voted α β γ) _ _ votedEquiv.symm
    (fun a1 a2 => (voted_compare_hmorph (votedEquiv.symm a1) (votedEquiv.symm a2)).symm)
    inferInstance

end Voted


instance {α β γ : Type} [FinEnum α] [FinEnum β] [FinEnum γ] : FinEnum (Voted α β γ) :=
  FinEnum.ofEquiv _
    { toFun := fun v => (v.bal, v.slot, v.val)
      invFun := fun (b, s, v) => { bal := b, slot := s, val := v }
      left_inv := by intro v; cases v; simp
      right_inv := by intro x; simp }


instance [FinEnum α] : Veil.Enumeration α where
  -- allValues := FinEnum.toList α
  allValues := FinEnum.toList α
  complete := FinEnum.mem_toList


structure Decree (β γ : Type) where
  slot : β
  val  : γ
deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Hashable, Ord, Repr

namespace Decree

def decreeEquiv : Decree β γ ≃ (β × γ) where
  toFun d := (d.slot, d.val)
  invFun := fun (s, v) => { slot := s, val := v }
  left_inv := by intro d; cases d; rfl
  right_inv := by intro p; rfl

theorem decree_compare_hmorph
  [Ord β] [Ord γ]
  (d1 d2 : Decree β γ) :
  compare d1 d2 = compare (decreeEquiv d1) (decreeEquiv d2) := by
  simp [Ord.compare, decreeEquiv, instOrdDecree.ord]

instance instTransOrdForDecree
[Ord β] [Ord γ]
[Std.TransOrd β]
[Std.TransOrd γ]
: Std.TransOrd (Decree β γ) :=
  @Std.TransOrd.by_equiv (β × γ) (Decree β γ) _ _ decreeEquiv.symm
    (fun a1 a2 => (decree_compare_hmorph (decreeEquiv.symm a1) (decreeEquiv.symm a2)).symm)
    inferInstance

instance instLawfulEqOrdForDecree
[Ord β] [Ord γ]
[Std.LawfulEqOrd β]
[Std.LawfulEqOrd γ]
: Std.LawfulEqOrd (Decree β γ) :=
  @Std.LawfulEqOrd.by_equiv (β × γ) (Decree β γ) _ _ decreeEquiv.symm
    (fun a1 a2 => (decree_compare_hmorph (decreeEquiv.symm a1) (decreeEquiv.symm a2)).symm)
    inferInstance
end Decree

instance FinEnumDecree {β γ : Type} [FinEnum β] [FinEnum γ] : FinEnum (Decree β γ) :=
  FinEnum.ofEquiv _
    { toFun := fun d => (d.slot, d.val)
      invFun := fun (s, v) => { slot := s, val := v }
      left_inv := by intro d; cases d; simp
      right_inv := by intro x; simp }

/-
Messages ==
[type : {"1a"}, bal : Ballots, from : Proposers] \ cup
[ type : {"1b"}, bal : Ballots,
  voted : SUBSET [bal : Ballots,
  slot : Slots,
  val : Values],
  from : Acceptors]
[type : {"2a"}, bal : Ballots, decrees : SUBSET [slot : Slots, val : Values], from : Proposers]
[type : {"2b"}, bal : Ballots, slot : Slots, val : Values, from : Acceptors]
-/
type SlotSet
type VotedSet
type DecreeSet
type MsgSet

inductive MsgType where
  | Phase1a
  | Phase1b
  | Phase2a
  | Phase2b
deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr

instance : FinEnum MsgType :=
  FinEnum.ofList
    [MsgType.Phase1a, MsgType.Phase1b, MsgType.Phase2a, MsgType.Phase2b]
    (by simp; intro x; cases x <;> simp )

instance : Std.TransOrd MsgType where
  eq_swap := by intro a b; cases a <;> cases b <;> decide
  isLE_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide

instance : Std.LawfulEqOrd MsgType where
  compare_self := by intro a; cases a <;> decide
  eq_of_compare := by intro a b; cases a <;> cases b <;> decide

structure Msg (ac val blt slt vcont dcont : Type) where
  msgType : MsgType
  src : ac
  val : val
  bal : blt
  slot : slt
  decrees : dcont
  voted : vcont
deriving Inhabited, DecidableEq, Lean.ToJson, Hashable, Ord, Repr


namespace Msg

def msgEquiv : Msg ac valT blt slt vcont dcont ≃ (MsgType × ac × valT × blt × slt × dcont × vcont) where
  toFun m := (m.msgType, m.src, m.val, m.bal, m.slot, m.decrees, m.voted)
  invFun := fun (t, s, v, b, sl, d, vo) =>
    { msgType := t, src := s, val := v, bal := b, slot := sl, decrees := d, voted := vo }
  left_inv := by intro m; cases m; rfl
  right_inv := by intro p; rfl

theorem msg_compare_hmorph
  [Ord ac] [Ord valT] [Ord blt] [Ord slt] [Ord vcont] [Ord dcont]
  (m1 m2 : Msg ac valT blt slt vcont dcont) :
  compare m1 m2 = compare (msgEquiv m1) (msgEquiv m2) := by
  simp [Ord.compare, msgEquiv, instOrdMsg.ord]

end Msg

instance {ac val blt slt vcont dcont : Type}
    [FinEnum ac] [FinEnum val] [FinEnum blt]
    [FinEnum slt] [FinEnum vcont] [FinEnum dcont] :
    FinEnum (Msg ac val blt slt vcont dcont) :=
  FinEnum.ofEquiv _
    {
      toFun := fun m => (m.msgType, m.src, m.val, m.bal, m.slot, m.decrees, m.voted)
      invFun := fun (t, s, v, b, sl, d, vo) =>
        { msgType := t, src := s, val := v, bal := b, slot := sl, decrees := d, voted := vo }
      left_inv := by intro m; cases m; simp
      right_inv := by intro x; simp
    }


instance instTransOrdForMsg
[Ord ac] [Ord val] [Ord blt] [Ord slt] [Ord vcont] [Ord dcont]
[Std.TransOrd ac] [Std.TransOrd val] [Std.TransOrd blt] [Std.TransOrd slt] [Std.TransOrd vcont] [Std.TransOrd dcont]
: Std.TransOrd (Msg ac val blt slt vcont dcont) :=
  @Std.TransOrd.by_equiv (MsgType × ac × val × blt × slt × dcont × vcont) (Msg ac val blt slt vcont dcont) _ _ Msg.msgEquiv.symm
    (fun a1 a2 => (Msg.msg_compare_hmorph (Msg.msgEquiv.symm a1) (Msg.msgEquiv.symm a2)).symm)
    inferInstance

instance instLawfulOrdForMsg
[Ord ac] [Ord val] [Ord blt] [Ord slt] [Ord vcont] [Ord dcont]
[Std.LawfulEqOrd ac] [Std.LawfulEqOrd val] [Std.LawfulEqOrd blt] [Std.LawfulEqOrd slt] [Std.LawfulEqOrd vcont] [Std.LawfulEqOrd dcont]
: Std.LawfulEqOrd (Msg ac val blt slt vcont dcont) :=
  @Std.LawfulEqOrd.by_equiv (MsgType × ac × val × blt × slt × dcont × vcont) (Msg ac val blt slt vcont dcont) _ _ Msg.msgEquiv.symm
    (fun a1 a2 => (Msg.msg_compare_hmorph (Msg.msgEquiv.symm a1) (Msg.msgEquiv.symm a2)).symm)
    inferInstance


instantiate tot : TotalOrderWithZero ballot
-- ASSUME QuorumAssumption ==
--           /\ Quorums \subseteq SUBSET Acceptors
--           /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
immutable individual one : ballot
instantiate voteTset : TSet (Voted ballot slot value) VotedSet
instantiate slotTset : TSet slot SlotSet
instantiate decreeSet : TSet (Decree slot value) DecreeSet
instantiate msgTset : TSet (Msg acceptor value ballot slot VotedSet DecreeSet) MsgSet


immutable relation member (A : acceptor) (Q : quorum)
function acceptorVoted (acceptor : acceptor) : VotedSet
function acceptorMaxBal (acceptor : acceptor) : ballot
-- relation msgs (m : Msg acceptor ballot slot VotedSet)
-- individual msgs : MsgSet
individual sent : MsgSet

#gen_state


theory ghost relation lt (x y : ballot) := (tot.le x y ∧ x ≠ y)
theory ghost relation next (x y : ballot) := (lt x y ∧ ∀ z, lt x z → tot.le y z)
assumption [zero_one] next tot.zero one
-- ASSUME QuorumAssumption ==
--           /\ Quorums \subseteq SUBSET Acceptors
--           /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : acceptor), member r q1 ∧ member r q2

after_init {
  sent := msgTset.empty
  acceptorVoted A := voteTset.empty
  acceptorMaxBal M :=  tot.zero
}

-- Phase1a(p) == \E b \in Ballots:
-- Send({[type |-> "1a", from |-> p, bal |-> b]})
-- Ballots == Nat
-- Slots == Nat
-- VARIABLES sent
-- vars == <<sent>>
-- Send(m) == sent' = sent \cup m
-- None == CHOOSE v : v \notin Values

procedure Send (m : MsgSet) {
  -- sent := msgTset.insert m sent
  sent := msgTset.toList m |>.foldl (fun acc msg => msgTset.insert msg acc) sent
}
-- (***************************************************************************)
-- (* Phase 1a: Executed by a proposer, it selects a ballot number on which   *)
-- (* Phase 1a has never been initiated. This number is sent to any set of    *)
-- (* acceptors which contains at least one quorum from Quorums. Trivially it *)
-- (* can be broadcasted to all Acceptors. For safety, any subset of          *)
-- (* Acceptors would suffice. For liveness, a subset containing at least one *)
-- (* Quorum is needed.                                                       *)
-- (***************************************************************************)
-- Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
--               /\ Send([type |-> "1a", bal |-> b])
--               /\ UNCHANGED <<acceptorVoted, acceptorMaxBal>>

--   msgType : String
--   src : acceptorSet
--   bal : ballot
--   decrees : votedSet
--   voted : votedSet
-- deriving Inhabited, DecidableEq

/-
Phase1a(p) == \E b \in Ballots:
  Send({[type |-> "1a", from |-> p, bal |-> b]})
-/
action Phase1a (p : acceptor) {
  let b ← pick ballot
  let sentMsg := {
    msgType := MsgType.Phase1a,
    src := p,
    val := default,
    bal := b,
    slot := default,
    decrees := default,
    voted := default}
  Send (msgTset.insert sentMsg msgTset.empty)
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

-- voteds(a) == {[bal |-> m.bal, slot |-> m.slot, val |-> m.val]: m \in {m \in sent: m.type = "2b" /\ m.from = a}}
-- set_option trace.veil.desugar true
procedure voteds (a : acceptor) {
  let voteSet' : VotedSet :=
    msgTset.map (msgTset.filter sent (fun m =>  m.msgType = MsgType.Phase2b ∧ m.src = a ))
     (fun m =>
      { bal    := m.bal,
        slot   := m.slot,
        val    := m.val : Voted ballot slot value })
  return voteSet'
}

-- PartialBmax(T) ==
--   {t \in T : \A t1 \in T : t1.slot = t.slot => t1.bal =< t.bal}
procedure PartialBmax (T : VotedSet) {
  let partialBmaxSet' := voteTset.filter T (fun t =>
    voteTset.toList T |>.all (fun t1 =>
      decide $ t1.slot = t.slot → (tot.le t1.bal t.bal) ))
  return partialBmaxSet'
}


-- Phase1b(a) == \E m \in sent:
--   /\ m.type = "1a"
--   /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal > m2.bal
--   /\ Send({[type |-> "1b", from |-> a, bal |-> m.bal, voted |-> PartialBmax(voteds(a))]})
action Phase1b (a : acceptor) {
  let m :| msgTset.contains m sent ∧  m.msgType = MsgType.Phase1a
  require ∀ m2, msgTset.contains m2 sent →
    ( (m2.msgType = MsgType.Phase1b ∨ m2.msgType = MsgType.Phase2b) ∧ m2.src = a ) → lt m2.bal m.bal
  let votedSet ← voteds a
  let partialBmaxSet ← PartialBmax votedSet
  let replyMsg : Msg acceptor value ballot slot VotedSet DecreeSet := {
    msgType := MsgType.Phase1b,
    src := a,
    val := default,
    bal := m.bal,
    slot := default,
    decrees := default,
    voted := partialBmaxSet
  }
  Send (msgTset.insert replyMsg msgTset.empty)
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
procedure Bmax (T : VotedSet) {
  let partialBmaxSet ← PartialBmax T
  let result : DecreeSet :=
    voteTset.map partialBmaxSet (fun t =>
      { slot := t.slot,
        val := t.val : Decree slot value })
  return result
}

-- FreeSlots(T) ==
--   {s \in Slots : ~ \E t \in T : t.slot = s}
ghost relation FreeSlots (T : VotedSet) (s : slot) :=
  ∀ t, voteTset.contains t T → t.slot ≠ s

-- NewProposals(T) ==
--   (CHOOSE D \in SUBSET [slot : FreeSlots(T), val : Values] \ {}:
--     \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2)
  -- let result := slotTset.toList D |>.map (fun s =>
  --   { slot := s, val := default : Decree slot value })
  -- let newProposalsSet := result.foldl (fun acc d =>
  --   decreeSet.insert d acc) decreeSet.empty
  -- return newProposalsSet
procedure NewProposals (T : VotedSet) {
  let D ← pick SlotSet
  require slotTset.count D > 0
  require ∀ s, slotTset.contains s D → FreeSlots T s
  let slotList := slotTset.toList D
  let result := slotList.foldl (fun acc r =>
    /-TODO -/
    decreeSet.insert { slot := r, val := default } acc) decreeSet.empty
  assume ∀d1 d2, decreeSet.contains d1 result →
    decreeSet.contains d2 result →
    d1.slot = d2.slot → d1 = d2
  return result
}

-- ProposeDecrees(T) ==
--   Bmax(T) \cup NewProposals(T)
procedure ProposeDecrees (T : VotedSet) {
  let bmaxSet ← Bmax T
  let newProposalsSet ← NewProposals T
  let proposeDecreesSet := decreeSet.union bmaxSet newProposalsSet
  return proposeDecreesSet
}


-- VS(S, Q) == UNION {m.voted: m \in {m \in S: m.from \in Q}}
procedure VS (S : MsgSet) (Q : quorum) {
  let filteredMsgs := msgTset.filter S (fun m => member m.src Q)
  let result := msgTset.toList filteredMsgs
    |>.foldl (fun acc m => voteTset.union acc m.voted) voteTset.empty
  return result
}

-- Phase2a(p) == \E b \in Ballots:
--   /\ ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
--   /\ \E Q \in Quorums, S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}:
--        /\ \A a \in Q: \E m \in S: m.from = a
--        /\ Send({[type |-> "2a", from |-> p, bal |-> b, decrees |-> ProposeDecrees(VS(S, Q))]})
action Phase2a (p : acceptor) {
  let b ← pick ballot
  require ¬ (∃ m, msgTset.contains m sent ∧ m.msgType = MsgType.Phase2a ∧ m.bal = b)
  let Q ← pick quorum
  -- let S ← pick MsgSet
  let S :| ∀ m, msgTset.contains m S → m.msgType = MsgType.Phase1b ∧ m.bal = b
  require ∀ a, member a Q → ∃ m, msgTset.contains m S ∧ m.src = a
  let vsSet ← VS S Q
  let proposeDecreesSet ← ProposeDecrees vsSet
  let decreesMsgSet := decreeSet.map proposeDecreesSet (fun d =>
    { msgType := MsgType.Phase2a,
      src := p,
      val := default,
      bal := b,
      slot := default,
      decrees := decreeSet.insert d decreeSet.empty,
      voted := default : Msg acceptor value ballot slot VotedSet DecreeSet} )
  Send decreesMsgSet
}



-- (***************************************************************************)
-- (* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
-- (* the highest that it has seen, it votes for the all the message's values *)
-- (* in ballot b.                                                            *)
-- (***************************************************************************)
-- Phase2b(a) == \E m \in sent:
--   /\ m.type = "2a"
--   /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal >= m2.bal
--   /\ Send({[type |-> "2b", from |-> a, bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees})
action Phase2b (a : acceptor) {
  require msgTset.count = 0
  let m :| msgTset.contains m sent ∧ m.msgType = MsgType.Phase2a
  require ∀ m2, msgTset.contains m2 sent →
    ( (m2.msgType = MsgType.Phase1b ∨ m2.msgType = MsgType.Phase2b) ∧ m2.src = a ) → tot.le m2.bal m.bal
  let replyMsgSet := decreeSet.map m.decrees (fun d =>
      { msgType := MsgType.Phase2b,
        src := a,
        val := d.val,
        bal := m.bal,
        slot := d.slot,
        decrees := default,
        voted := default : Msg acceptor value ballot slot VotedSet DecreeSet} )
  Send replyMsgSet
}

invariant [sent_not_empty] msgTset.count sent < 2

#gen_spec


-- set_option trace.veil.debug true
-- #Concretize
--   (Fin 1),  -- ballot
--   (Fin 1),  -- slot
--   (Fin 1),  -- value
--   (Fin 1),  -- acceptor
--   (Fin 1), -- quorum
--   (ExtTreeSet (Fin 1) compare),  -- SlotSet
--   (ExtTreeSet (Voted (Fin 1) (Fin 1) (Fin 1)) compare),  -- VotedSet
--   (ExtTreeSet (Decree (Fin 1) (Fin 1)) compare),  -- DecreeSet
--   (ExtTreeSet (Msg (Fin 1) (Fin 1) (Fin 1) (Fin 1) (ExtTreeSet (Voted (Fin 1) (Fin 1) (Fin 1)) compare) (ExtTreeSet (Decree (Fin 1) (Fin 1)) compare)) compare)  -- MsgSet

open Veil.ModelChecker

/- We need set a very large number for both `maxHeartbeats`
and `maxSize` to get all required instances infered automatically,
especially for `Inhabited`. -/
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2000

#time #model_check
{
  ballot := Fin 1,
  slot := Fin 1,
  value := Fin 1,
  acceptor := Fin 1,
  quorum := Fin 1,
  SlotSet := ExtTreeSet (Fin 1) compare,
  VotedSet := ExtTreeSet (Voted (Fin 1) (Fin 1) (Fin 1)) compare,
  DecreeSet := ExtTreeSet (Decree (Fin 1) (Fin 1)) compare,
  MsgSet := ExtTreeSet (Msg (Fin 1) (Fin 1) (Fin 1) (Fin 1) (ExtTreeSet (Voted (Fin 1) (Fin 1) (Fin 1)) compare) (ExtTreeSet (Decree (Fin 1) (Fin 1)) compare)) compare
}
{
  one := 1,
  member := fun a q => true
}




end MultiPaxosUs
