import Veil
import Veil.DSL.Random.ExtractUtil
import Veil.DSL.Random.Extract
import Veil.DSL.Random.Main

/-
  This is a simplified version of the NOPaxos protocol, without view
  changes. As such, the leader is modelled as fixed.
-/
veil module NOPaxos

type replica -- replica ID
enum replica_state { st_normal, st_gap_commit } -- we don't model view changes
type seq_t
type value
type quorum

instantiate seq : TotalOrderWithZero seq_t
@[actSimp, invSimp] abbrev lt (x y : seq_t) : Prop := (seq.le x y ∧ x ≠ y)
@[actSimp, invSimp] abbrev next (x y : seq_t) : Prop := (lt seq_t x y ∧ ∀ z, lt seq_t x z → seq.le y z)

immutable individual one : seq_t
immutable individual no_op : value
-- We don't model view changes, so the leader is fixed
immutable individual leader : replica

immutable relation member (R : replica) (Q : quorum) : Bool

-- Sequencer, indicating the _next_ message number to be sequenced
-- NOTE: We don't model view changes (which can happen due to session termination),
-- so we only have one sequencer.
individual s_seq_msg_num : seq_t

-- Replica
relation r_log_len (r : replica) (i : seq_t) : Bool
relation r_log (r : replica) (i : seq_t) (v : value) : Bool
relation r_sess_msg_num (r : replica) (i : seq_t) : Bool   -- the expected _next_ message number
relation r_gap_commit_reps (r : replica) (p : replica) : Bool
relation r_current_gap_slot (r : replica) (i : seq_t) : Bool
relation r_replica_status (r : replica) (s : replica_state) : Bool

-- Network
relation m_client_request (v : value) : Bool
relation m_marked_client_request  (dest : replica) (v : value) (sess_msg_num : seq_t) : Bool
relation m_request_reply (sender : replica) (request : value) (log_slot_num : seq_t) : Bool
relation m_slot_lookup (dest : replica) (sender : replica) (sess_msg_num : seq_t) : Bool
relation m_gap_commit (dest : replica) (slot_num : seq_t) : Bool
relation m_gap_commit_rep (dest : replica) (sender : replica) (slot_num : seq_t) : Bool

-- Ghost state
relation gh_committed (s : seq_t) (v : value) : Bool

#gen_state

assumption [zero_one] next seq_t seq.zero one
assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : replica), member r q1 ∧ member r q2

after_init {
  -- Arrays in TLA+ are 1-indexed, and we follow the same convention here
  s_seq_msg_num := one;

  r_log_len R I := decide $ I = seq.zero
  r_log R I V := false
  r_sess_msg_num R I := decide $ I = one
  r_gap_commit_reps R P := false
  r_current_gap_slot R I := decide $ I = seq.zero
  r_replica_status R S := decide $ S = st_normal

  m_client_request V := false
  m_marked_client_request D V SMN := false
  m_request_reply S V LSN := false
  m_slot_lookup D S SMN := false
  m_gap_commit D SN := false
  m_gap_commit_rep D S SN := false

  gh_committed S V := false
}

procedure succ(n : seq_t) {
  let k :| next seq_t n k
  return k
}

procedure replace_item (r : replica) (i : seq_t) (v : value) {
  let len :| r_log_len r len
  let next_len ← succ len
  if seq.le i next_len then
    if i = next_len then
      r_log_len r I := decide $ I = i
    r_log r i V := decide $ V = v
}

-- action client_sends_request (v : value) {
--   require v ≠ no_op
action client_sends_request {
  let v :| v ≠ no_op
  m_client_request v := true
}

-- Sequencer handles the client request
-- action handle_client_request (m_value : value) {
--   require m_client_request m_value
action handle_client_request {
  let m_value :| m_client_request m_value
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
  r_log_len r I := decide $ I = next_len
  return next_len
}

procedure increase_session_number (r : replica) {
  let smn :| r_sess_msg_num r smn
  let next_smn ← succ smn
  r_sess_msg_num r I := decide $ I = next_smn
  return next_smn
}

-- Normal case of `HandleMarkedClientRequest`
-- action handle_marked_client_request_normal (r : replica) (m_value : value) (m_sess_msg_num : seq_t) {
--   require m_marked_client_request r m_value m_sess_msg_num
--   require r_replica_status r st_normal
action handle_marked_client_request_normal {
  let (r, m_value, m_sess_msg_num) :| (m_marked_client_request r m_value m_sess_msg_num ∧ r_replica_status r st_normal)
  let smn :| r_sess_msg_num r smn
  require m_sess_msg_num = smn
  let _new_smn ← increase_session_number r
  let new_len ← append_to_log r m_value
  m_request_reply r m_value new_len := true
}


procedure send_gap_commit (r : replica) {
  require r = leader
  require r_replica_status r st_normal
  let len :| r_log_len r len
  let slot ← succ len
  r_replica_status r S := decide $ S = st_gap_commit
  r_gap_commit_reps r P := false
  r_current_gap_slot r I := decide $ I = slot
  m_gap_commit R slot := true
}

-- Drop notification case of `HandleMarkedClientRequest`
action handle_marked_client_drop_notification (r : replica) (m_value : value) (m_sess_msg_num : seq_t) {
  require m_marked_client_request r m_value m_sess_msg_num
  require r_replica_status r st_normal
-- action handle_marked_client_drop_notification {
--   let (r, m_value, m_sess_msg_num) :| (m_marked_client_request r m_value m_sess_msg_num ∧ r_replica_status r st_normal)
  let smn :| r_sess_msg_num r smn
  -- NOTE: this is the condition in the TLA+ spec, but it means that
  -- a drop notification cannot be sent for the first session number,
  -- which seems incorrect.
  require lt seq_t smn m_sess_msg_num
  if r = leader then
    send_gap_commit r
  else
    m_slot_lookup leader r smn := true
}

-- action handle_slot_lookup (r : replica) (m_sender : replica) (m_sess_msg_num : seq_t) {
--   require m_slot_lookup r m_sender m_sess_msg_num
--   require r_replica_status r st_normal
--   require r = leader
action handle_slot_lookup {
  let (r, m_sender, m_sess_msg_num) :| (m_slot_lookup r m_sender m_sess_msg_num ∧ r_replica_status r st_normal ∧ r = leader)
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
    if v : r_log r slot v then
      m_marked_client_request m_sender v m_sess_msg_num := true
    else
      -- Nothing to undo
      pure ()
  if slot = (← succ len) then
    send_gap_commit r
}

-- Replica r (or the leader) receives GapCommit
-- action handle_gap_commit (r : replica) (m_slot_num : seq_t) {
--   require m_gap_commit r m_slot_num
action handle_gap_commit {
  let (r, m_slot_num) :| m_gap_commit r m_slot_num
  let len :| r_log_len r len
  -- NOTE: this condition ensures that the skipping operation (the `if` block
  -- below) is meaningful, or intuitively "neither too early nor too late"
  require seq.le m_slot_num len ∨ next seq_t len m_slot_num
  let smn :| r_sess_msg_num r smn
  replace_item r m_slot_num no_op
  if lt seq_t len m_slot_num then
    let  _new_smn ← increase_session_number r
  m_gap_commit_rep leader r m_slot_num := true
  m_request_reply r no_op m_slot_num := true
}

-- action handle_gap_commit_rep (r : replica) (m_sender : replica) (m_slot_num : seq_t) {
--   require m_gap_commit_rep r m_sender m_slot_num
--   require r_replica_status r st_gap_commit
--   require r = leader
--   require r_current_gap_slot r m_slot_num
action handle_gap_commit_rep {
  let (r, m_sender, m_slot_num) :| (m_gap_commit_rep r m_sender m_slot_num ∧ r_replica_status r st_gap_commit ∧ r = leader ∧ r_current_gap_slot r m_slot_num)
  r_gap_commit_reps r m_sender := true
  if (r_gap_commit_reps r r) ∧ (∃ (q:quorum), ∀ (p:replica),
    member p q → r_gap_commit_reps r p) then
    r_replica_status r S := decide $ S = st_normal
}

-- action client_commit (s : seq_t) (v : value) {
--   require ∃ (q:quorum), ∀ (p:replica), member p q → m_request_reply p v s
--   require m_request_reply leader v s
action client_commit {
  let (s, v) :| ((∃ (q:quorum), ∀ (p:replica), member p q → m_request_reply p v s) ∧ m_request_reply leader v s)
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
invariant [valid_sess_msg_num] (r_log_len R I ∧ r_sess_msg_num R J) → next seq_t I J
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

#time #gen_spec

#time #check_invariants

end NOPaxos

veil module NOPaxos

variable [FinEnum quorum] [FinEnum value] [FinEnum seq_t] [FinEnum replica]
variable [DecidableEq replica_state] [FinEnum replica_state]
variable [insta : DecidableRel seq.le] [instb : DecidableRel (lt seq_t)] [instc : DecidableRel (next seq_t)]

#gen_computable
set_option maxHeartbeats 1600000 in
#time #gen_executable

simple_deriving_repr_for Reader
simple_deriving_repr_for State

deriving instance Repr for Label
deriving instance Inhabited for Label
deriving instance Inhabited for State
deriving instance Inhabited for Reader

end NOPaxos

#deriveGen NOPaxos.Label
#deriveGen! NOPaxos.State
deriving_enum_instance_for NOPaxos.replica_state
