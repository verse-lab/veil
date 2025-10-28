import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
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
  -- r_current_gap_slot R I := I == seq.zero
  -- r_replica_status R S := S == st_normal

  -- m_client_request V := false
  -- m_marked_client_request D V SMN := false
  -- m_request_reply S V LSN := false
  -- m_slot_lookup D S SMN := false
  -- m_gap_commit D SN := false
  -- m_gap_commit_rep D S SN := false

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
  -- let next_slot ← succ slot
  -- s_seq_msg_num := next_slot
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
  -- let _new_smn ← increase_session_number r
  -- let new_len ← append_to_log r m_value
  -- m_request_reply r m_value new_len := true
}


procedure send_gap_commit (r : replica) {
  require r = leader
  require r_replica_status r st_normal
  let len :| r_log_len r len
  let slot ← succ len
  r_replica_status r S := S == st_gap_commit
  -- r_gap_commit_reps r P := false
  -- r_current_gap_slot r I := I == slot
  -- m_gap_commit R slot := true
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

-- action handle_slot_lookup (r : replica) (m_sender : replica) (m_sess_msg_num : seq_t) {
--   require m_slot_lookup r m_sender m_sess_msg_num
--   require r_replica_status r st_normal
--   require r = leader
--   let len :| r_log_len r len
--   let smn :| r_sess_msg_num r smn
--   -- Note: in TLA+ the slot is computed as
--   -- `logSlotNum == Len(vLog[r]) + 1 - (vSessMsgNum[r] - m.sessMsgNum)`
--   -- which calculates the offset from the tail of the log;
--   -- however, with no view changes, this is equivalent to simply taking
--   -- the index of the incoming m.sessMsgNum
--   -- (i.e., with no view changes, we should have `vSessMsgNum[r]` = `Len(vLog[r]) + 1`)
--   let slot := m_sess_msg_num
--   if seq.le slot len then
--     -- NOTE: cannot make this into a pick-such-that because it might not exist
--     if v : r_log r slot v then
--       m_marked_client_request m_sender v m_sess_msg_num := true
--     else
--       -- Nothing to undo
--       pure ()
--   if slot = (← succ len) then
--     send_gap_commit r
-- }


-- Replica r (or the leader) receives GapCommit
-- action handle_gap_commit (r : replica) (m_slot_num : seq_t) {
--   require m_gap_commit r m_slot_num
--   let len :| r_log_len r len
--   -- NOTE: this condition ensures that the skipping operation (the `if` block
--   -- below) is meaningful, or intuitively "neither too early nor too late"
--   require seq.le m_slot_num len ∨ next len m_slot_num
--   let smn :| r_sess_msg_num r smn
--   replace_item r m_slot_num no_op
--   if lt len m_slot_num then
--     let  _new_smn ← increase_session_number r
--   m_gap_commit_rep leader r m_slot_num := true
--   let st :| r_replica_status r st
--   m_request_reply r no_op m_slot_num := true
-- }

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
#time #gen_spec

-- #time #check_invariants

open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- #time #check_invariants
section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil Extract


variable [FinEnum replica] [Hashable replica]
variable [FinEnum replica_state] [Hashable replica_state]
variable [FinEnum value] [Hashable value]
variable [FinEnum quorum] [Hashable quorum]
variable [FinEnum seq_t] [Hashable seq_t]


def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instDecidableEqForComponents' (f : State.Label)
  : DecidableEq (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instDecidableEqForComponents'' (f : State.Label)
  : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents (f : State.Label)
  : Hashable (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents' (f : State.Label)
  : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance


-- #reduce (⌞? State.Label.toCodomain ⌟) State.Label.s_seq_msg_num
-- theorem test : ((⌞? State.Label.toCodomain ⌟) State.Label.s_seq_msg_num) → True := by
--   dsimp [IteratedProd', State.Label.toCodomain]


abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  -- | State.Label.s_seq_msg_num => (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.s_seq_msg_num)
  | State.Label.s_seq_msg_num => ((⌞? State.Label.toCodomain ⌟) State.Label.s_seq_msg_num)
  | State.Label.r_log_len => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.r_log_len)
  | State.Label.r_log => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.r_log)
  | State.Label.r_sess_msg_num => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.r_sess_msg_num)
  | State.Label.r_gap_commit_reps => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.r_gap_commit_reps)
  | State.Label.r_current_gap_slot => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.r_current_gap_slot)
  | State.Label.r_replica_status => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.r_replica_status)
  | State.Label.m_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_client_request)
  | State.Label.m_marked_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_marked_client_request)
  | State.Label.m_request_reply => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_request_reply)
  | State.Label.m_slot_lookup => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_slot_lookup)
  | State.Label.m_gap_commit  => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_gap_commit)
  | State.Label.m_gap_commit_rep => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_gap_commit_rep)
  | State.Label.gh_r_received_sequenced_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_r_received_sequenced_client_request)
  | State.Label.gh_r_received_drop_notification => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_r_received_drop_notification)
  | State.Label.gh_committed => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_committed)

instance instReprForComponents  [Repr replica] [Repr replica_state] [Repr value] [Repr quorum] [Repr seq_t] (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, IteratedProd', List.foldr, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance

-- #simp [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] FieldConcreteType Nat .leader
  -- Veil.CanonicalField (State.Label.toDomain Nat .pending) (State.Label.toCodomain Nat .pending)

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;>
  dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
  exact default

instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) := -- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
    | State.Label.s_seq_msg_num => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
    | State.Label.r_log_len =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_log_len)
    | State.Label.r_log =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_log)
    | State.Label.r_sess_msg_num =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_sess_msg_num)
    |  State.Label.r_gap_commit_reps =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_gap_commit_reps)
    | State.Label.r_current_gap_slot =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_current_gap_slot)
    | State.Label.r_replica_status =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_replica_status)
    | State.Label.m_client_request =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_client_request)
    | State.Label.m_marked_client_request =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_marked_client_request)
    | State.Label.m_request_reply =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_request_reply)
    | State.Label.m_slot_lookup =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_slot_lookup)
    | State.Label.m_gap_commit =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit)
    | State.Label.m_gap_commit_rep =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit_rep)
    | State.Label.gh_r_received_sequenced_client_request =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_sequenced_client_request)
    | State.Label.gh_r_received_drop_notification =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_drop_notification)
    | State.Label.gh_committed =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_committed)

#check  FinsetLike

instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
    | State.Label.s_seq_msg_num => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
    | State.Label.r_log_len =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_log_len)
    | State.Label.r_log =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_log)
    | State.Label.r_sess_msg_num =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_sess_msg_num)
    | State.Label.r_gap_commit_reps =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_gap_commit_reps)
    | State.Label.r_current_gap_slot =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_current_gap_slot)
    | State.Label.r_replica_status =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.r_replica_status)
    | State.Label.m_client_request =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_client_request)
    | State.Label.m_marked_client_request =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_marked_client_request)
    | State.Label.m_request_reply =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_request_reply)
    | State.Label.m_slot_lookup =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_slot_lookup)
    | State.Label.m_gap_commit =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit)
    | State.Label.m_gap_commit_rep =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit_rep)
    | State.Label.gh_r_received_sequenced_client_request =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_sequenced_client_request)
    | State.Label.gh_r_received_drop_notification =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_drop_notification)
    | State.Label.gh_committed =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_committed)
end


attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin
    [FinEnum replica] [Hashable replica]
    [FinEnum replica_state] [Hashable replica_state]
    [FinEnum value] [Hashable value]
    [FinEnum quorum] [Hashable quorum]
    [FinEnum seq_t] [Hashable seq_t]
  injection_end => NextAct'

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum replica] [Hashable replica]
    [FinEnum replica_state] [Hashable replica_state]
    [FinEnum value] [Hashable value]
    [FinEnum quorum] [Hashable quorum]
    [FinEnum seq_t] [Hashable seq_t]
  injection_end

#check initMultiExec
#check nextActMultiExec


instance (n : Nat): TotalOrderWithZero (Fin n.succ) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega
  zero := ⟨0, by simp⟩
  zero_le := by simp


deriving_enum_instance_for replica_state

instance (n : Nat) : DecidableRel (TotalOrderWithZero.le (t := Fin n.succ)) := by
  dsimp [TotalOrderWithZero.le] ; infer_instance_for_iterated_prod


#check lt

variable {n_replica n_value n_seq_t : Nat}

local macro "⌞ " t:term " ⌟" : term =>
  `(((($t (Fin n_replica.succ) replica_state (Fin n_seq_t.succ.succ) (Fin n_value.succ) (Fin n_replica.succ)))))

local macro "⌞State⌟" : term =>
  `(((⌞ State ⌟) ⌞ FieldConcreteType ⌟))

local macro "⌞_ " t:term " _⌟" : term =>
  `((⌞ $t (⌞ Theory ⌟) (⌞State⌟) ⌟))

local macro "⌞__ " t:term " __⌟" : term =>
  `((⌞ $t (⌞ Theory ⌟) (⌞State⌟) ⌟) ⌞ FieldConcreteType ⌟)

local instance (th : ⌞ Theory ⌟) : Decidable (lt x y th) := by
  dsimp [lt]
  infer_instance

#check next
local instance  (th : ⌞ Theory ⌟) : Decidable (next x y th) := by infer_instance

#print instFinEnumReplica_state

instance FinEnumReplica_state : FinEnum replica_state :=
FinEnum.ofList [replica_state.st_normal, replica_state.st_gap_commit] instFinEnumReplica_state._proof_1

instance : Hashable replica_state where
  hash s :=
    match s with
    | .st_normal => hash 0
    | .st_gap_commit => hash 1

#Concretize (Fin 1), replica_state, (Fin 1), (Fin 2), (Fin 1)

simple_deriving_repr_for' State

simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory

instance [Hashable α] [BEq α] : Hashable (Std.HashSet α) where
  hash s :=
    /- `Hash collision `-/
    s.fold (init := 0) fun acc a => acc + (hash a)


instance : BEq (FieldConcreteType (Fin 1) replica_state (Fin 1) (Fin 2) (Fin 1) State.Label.s_seq_msg_num) :=
by
  dsimp [FieldConcreteType, State.Label.toCodomain] ;
  infer_instance

instance : Hashable (FieldConcreteType (Fin 1) replica_state (Fin 1) (Fin 2) (Fin 1) State.Label.s_seq_msg_num) :=
by
  dsimp [FieldConcreteType, State.Label.toCodomain]
  infer_instance

#assembleInsts

#print instBEqStateConcrete
#print instHashableStateConcrete

-- theorem ttt: FieldConcreteType (Fin 1) replica_state (Fin 1) (Fin 1) (Fin 1) State.Label.s_seq_msg_num → True := by
--   dsimp [FieldConcreteType, State.Label.toCodomain]

instance : (rd : TheoryConcrete) → (st : StateConcrete)
    → Decidable ((fun ρ σ => lead_gap_commits ρ σ) rd st) := by
  intro rd st
  unfold lead_gap_commits
  infer_instance

#check lead_gap_commits

-- def rd₀ :=   { one := 1, no_op := 0, member := fun a b => a ∈ b.val,leader := 0 }

#print nextVeilMultiExecM
-- def st₀ := (((afterInit initVeilMultiExecM { one := 1, no_op := 0, member := fun a b => a = b,leader := 0 } default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
-- #check st₀

instance : OfNat (FieldConcreteType (Fin 1) replica_state (Fin 1) (Fin 2) (Fin 1)
                             State.Label.s_seq_msg_num) 0 where
  ofNat := (0 : Fin 1)

#print initVeilMultiExecM

    -- { one := ⟨1, Nat.succ_le_succ <| Nat.succ_le_succ <| Nat.zero_le _⟩
    --   no_op := ⟨0, Nat.zero_lt_succ _⟩
    --   member := fun a b => a ∈ b.val
    --   leader := leader }

def rd₀ : TheoryConcrete :=
  { one := 1, no_op := 0, member := fun a b => a == b, leader := 0 }
def st₀ := (((afterInit initVeilMultiExecM rd₀ default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
#eval st₀


#check nextVeilMultiExecM

def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => true) rd₀).snd
#eval modelCheckerResult'.seen.length

-- def modelCheckerResultxx := (runModelCheckerxx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => true) rd₀).snd
-- #eval modelCheckerResultxx.seen.length

#html createExpandedGraphDisplay (collectTrace modelCheckerResult').1 (collectTrace modelCheckerResult').2


end NOPaxos
