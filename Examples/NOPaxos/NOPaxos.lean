import Veil

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
@[actSimp, invSimp] abbrev lt (x y : seq_t) : Prop := (seq.le x y ∧ x ≠ y)
@[actSimp, invSimp] abbrev next (x y : seq_t) : Prop := (lt seq_t x y ∧ ∀ z, lt seq_t x z → seq.le y z)

immutable individual one : seq_t
immutable individual no_op : value
-- We don't model view changes, so the leader is fixed
immutable individual leader : replica

immutable relation member(R : replica) (Q : quorum)

-- Sequencer
individual s_seq_msg_num : seq_t

-- Replica
relation r_log_len (r : replica) (i : seq_t)
relation r_log (r : replica) (i : seq_t) (v : value)
relation r_sess_msg_num (r : replica) (i : seq_t)
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

assumption [zero_one] next seq_t seq.zero one
assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : replica), member r q1 ∧ member r q2

after_init {
  -- Arrays in TLA+ are 1-indexed, and we follow the same convention here
  s_seq_msg_num := one;

  r_log_len R I := I = seq.zero
  r_log R I V := False
  r_sess_msg_num R I := I = one
  r_gap_commit_reps R P := False
  r_current_gap_slot R I := I = seq.zero
  r_replica_status R S := S = st_normal

  m_client_request V := False
  m_marked_client_request D V SMN := False
  m_request_reply S V LSN := False
  m_slot_lookup D S SMN := False
  m_gap_commit D SN := False
  m_gap_commit_rep D S SN := False

  gh_r_received_sequenced_client_request R S := False
  gh_r_received_drop_notification R S := False
  gh_committed S V := False
}

procedure succ(n : seq_t) = {
  let k ← pick seq_t
  assume next seq_t n k
  return k
}

procedure replace_item (r : replica) (i : seq_t) (v : value) = {
  let len :| r_log_len r len
  let next_len ← succ len
  if seq.le i next_len then
    if i = next_len then
      r_log_len r I := I = i
    r_log r I V := V = v
}

action client_sends_request (v : value) = {
  require v ≠ no_op
  m_client_request v := True
}

-- Sequencer handles the client request
action handle_client_request (m_value : value) (s : seq_t) = {
  require m_client_request m_value
  let slot := s_seq_msg_num
  m_marked_client_request R m_value slot := True
  let next_slot ← succ slot
  s_seq_msg_num := next_slot
}

procedure append_to_log (r : replica) (v : value) = {
  let len :| r_log_len r len
  r_log r len v := True
  let next_len ← succ len
  r_log_len r I := I = next_len
  return next_len
}

procedure increase_session_number (r : replica) = {
  let smn :| r_sess_msg_num r smn
  let next_smn ← succ smn
  r_sess_msg_num r I := I = next_smn
  return next_smn
}

-- Normal case of `HandleMarkedClientRequest`
action handle_marked_client_request_normal (r : replica) (m_value : value) (m_sess_msg_num : seq_t) = {
  require m_marked_client_request r m_value m_sess_msg_num
  require r_replica_status r st_normal
  let len :| r_log_len r len
  let smn :| r_sess_msg_num r smn
  require m_sess_msg_num = smn
  gh_r_received_sequenced_client_request r m_sess_msg_num := True
  let _new_smn ← increase_session_number r
  let new_len ← append_to_log r m_value
  m_request_reply r m_value new_len := True
}

procedure send_gap_commit (r : replica) = {
  require r = leader
  require r_replica_status r st_normal
  let len :| r_log_len r len
  let slot ← succ len
  r_replica_status r S := S = st_gap_commit
  r_gap_commit_reps r P := False
  r_current_gap_slot r I := I = slot
  m_gap_commit r slot := True
}

-- Drop notification case of `HandleMarkedClientRequest`
action handle_marked_client_drop_notification (r : replica) (m_value : value) (m_sess_msg_num : seq_t) = {
  require m_marked_client_request r m_value m_sess_msg_num
  require r_replica_status r st_normal
  let smn :| r_sess_msg_num r smn
  require lt seq_t smn m_sess_msg_num
  gh_r_received_drop_notification r m_sess_msg_num := True
  if r = leader then
    send_gap_commit r
  else
    m_slot_lookup leader r smn := True
}

action handle_slot_lookup (r : replica) (m_sender : replica) (m_sess_msg_num : seq_t) = {
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
  let slot := m_sess_msg_num
  if seq.le slot len then
    -- NOTE: cannot make this into a pick-such-that because it might not exist
    if v : r_log r slot v then
      m_marked_client_request m_sender v m_sess_msg_num := True
    else
      -- Nothing to undo
      pure ()
  if slot = (← succ len) then
    send_gap_commit r
}


action client_commit (s : seq_t) (v : value) = {
  require ∃ (q:quorum), ∀ (p:replica), member p q → m_request_reply p v s
  gh_committed s v := True
}

safety [consistency] gh_committed S V1 ∧ gh_committed S V2 → V1 = V2

#time #gen_spec

#time #check_invariants

set_option veil.smt.model.minimize true

sat trace [can_sequence] {
  client_sends_request
  handle_client_request
} by bmc_sat

sat trace [can_sequence_same_request_twice] {
  client_sends_request
  handle_client_request
  handle_client_request
  assert (∃ (r : replica) (v : value) (s s' : seq_t), s ≠ s' ∧ m_marked_client_request r v s ∧ m_marked_client_request r v s')
} by bmc_sat

sat trace [can_handle_normal] {
  client_sends_request
  handle_client_request
  handle_marked_client_request_normal
} by bmc_sat


set_option maxHeartbeats 0

sat trace [can_get_dropped] {
  assert (∃ (r₁ r₂ : replica), r₁ ≠ r₂ ∧ ∀ r, r = r₁ ∨ r = r₂)
  client_sends_request
  handle_client_request
  assert (∃ (r : replica) (v : value) (s : seq_t), m_marked_client_request r v one)
  handle_marked_client_request_normal
  -- handle_marked_client_drop_notification
  -- handle_slot_lookup
} by bmc_sat


-- #time #check_invariants
set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
-- #time #check_action replica_recv_sequenced_client_request
-- #time #check_invariants!
-- #time #check_action replica_recv_gap_commit

end NOPaxos
