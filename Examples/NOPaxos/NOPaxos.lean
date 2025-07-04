import Veil

/-
  This is a simplified version of the NOPaxos protocol, without view
  changes. As such, the leader is modelled as fixed.
-/
veil module NOPaxos

type replica -- replica ID
enum r_state = { st_normal, st_gap_commit }
type sessnum -- session number
type value
type quorum

instantiate seq : TotalOrderWithMinimum sessnum
immutable individual one : sessnum
immutable individual no_op : value
-- We don't model view changes, so the leader is fixed
immutable individual leader : replica

-- Sequencer
-- the next session number to be assigned
individual s_sess_msg_num : sessnum

-- Replica
relation r_log (r : replica) (i : sessnum) (v : value)
relation r_log_len (r : replica) (i : sessnum)
relation r_replica_status (r : replica) (s : r_state)
-- the number of messages (requests or drop-notification) received by `r`
relation r_sess_msg_num (r : replica) (i : sessnum)

-- Network
-- message from the sequencer to the replicas with a sequenced client request
relation m_sequenced_client_request (dest : replica) (v : value) (s : sessnum)
-- message from a replica (or the leader) to the client with a request reply
relation m_request_reply (src : replica) (v : value) (s : sessnum)
-- replica `src` sends a slot lookup to the `leader` (implicit `dest`) for session number `s`
relation m_slot_lookup (src : replica) (s : sessnum)
-- leader replies to a slot lookup request from `dst` with a reply
relation m_slot_lookup_reply (dst : replica) (s : sessnum) (v : value)


-- Ghost state
relation gh_r_received_drop_notification (r : replica) (s : sessnum)

#gen_state

assumption [zero_one] seq.next seq.zero one

-- FIXME: define these automatically (with a `partial function` keyword)
invariant [r_log_coherence] r_log R I V1 ∧ r_log R I V2 → V1 = V2
invariant [r_log_len_coherence] r_log_len R I1 ∧ r_log_len R I2 → I1 = I2
invariant [r_replica_status_coherence] r_replica_status R S1 ∧ r_replica_status R S2 → S1 = S2
invariant [r_sess_msg_num_coherence] r_sess_msg_num R I1 ∧ r_sess_msg_num R I2 → I1 = I2

invariant [r_log_len_valid] r_log R I V ∧ r_log_len R L → seq.lt I L

after_init {
  s_sess_msg_num := seq.zero;

  r_log_len R I := I = seq.zero
  r_log R I V := False
  r_replica_status R S := S = st_normal
  r_sess_msg_num R I := I = s_sess_msg_num

  m_sequenced_client_request R V S := False
  m_request_reply R V S := False

  gh_r_received_drop_notification R S := False
}

procedure succ(n : sessnum) = {
  let k ← pick sessnum
  assume seq.next n k
  return k
}

-- Clients issue a request by it them to the sequencer, which gives it a
-- session number and broadcasts the request to all replicas.
action client_request (v : value) (s : sessnum) = {
  require v ≠ no_op;
  let slot := s_sess_msg_num
  m_sequenced_client_request R v slot := True
  let next_slot ← succ slot
  s_sess_msg_num := next_slot
}

-- Replica `r` receives a sequenced client request `v` with session number `s`.
action replica_recv_sequenced_client_request (r : replica) (v : value) (mslot : sessnum) = {
  require m_sequenced_client_request r v mslot
  require ¬ gh_r_received_drop_notification r mslot
  require r_replica_status r st_normal
  require r ≠ leader
  assert v ≠ no_op
  if logslot : r_log_len r logslot then
    if smn : r_sess_msg_num r smn then
      require smn = mslot -- we always process operations in order
      assert smn = logslot
      r_log r logslot v := True
      let next_len ← succ logslot
      r_log_len r I := I = next_len
      let next_smn ← succ smn
      r_sess_msg_num r I := I = next_smn
      m_request_reply r v logslot := True
}

-- Replica `r` receives a drop notification for session number `mslot`
action replica_recv_drop_notification (r : replica) (mslot : sessnum) = {
  require r_replica_status r st_normal
  require r ≠ leader
  require ¬ gh_r_received_drop_notification r mslot -- FIXME: we should be able to remove this
  if logslot : r_log_len r logslot then
    if smn : r_sess_msg_num r smn then
      require smn = mslot -- we always process operations in order
      gh_r_received_drop_notification r mslot := True
      assert smn = logslot
      -- Replica sends a `slot_lookup` request to the leader
      m_slot_lookup r mslot := True
}

-- Leader receives a sequenced client request `v` with session number `s`.
action leader_recv_sequenced_client_request (v : value) (mslot : sessnum) = {
  require m_sequenced_client_request leader v mslot
  require ¬ gh_r_received_drop_notification leader mslot
  require r_replica_status leader st_normal
  assert v ≠ no_op
  if logslot : r_log_len leader logslot then
    if smn : r_sess_msg_num leader smn then
      require smn = mslot -- we always process operations in order
      assert smn = logslot
      r_log leader logslot v := True
      let next_len ← succ logslot
      r_log_len leader I := I = next_len
      let next_smn ← succ smn
      r_sess_msg_num leader I := I = next_smn
      m_request_reply leader v logslot := True
}

-- Leader receives a slot lookup request for session number `mslot`
-- when it's in the normal state, i.e. the leader actually received the
-- value for this slot (rather than itself receiving a drop-notification)
action leader_recv_slot_lookup_normal (mr : replica) (mslot : sessnum) = {
  require m_slot_lookup mr mslot require
  r_replica_status leader st_normal
  if len : r_log_len leader len then
    if smn : r_sess_msg_num leader smn then
      -- If we have a value for this slot, we reply to the slot lookup request
      require seq.lt mslot len
      if v : r_log leader mslot v then
        m_slot_lookup_reply mr mslot v := True
}

invariant [no_spurious_sequencer_advance]
  ∀ (r : replica) (v : value) (s : sessnum),
    m_sequenced_client_request r v s → seq.lt s s_sess_msg_num

invariant [no_op_is_not_client_request]
  ∀ (r : replica) (v : value) (s : sessnum),
    m_sequenced_client_request r v s → v ≠ no_op

invariant [reply_implies_request_at_same_slot]
  ∀ (r : replica) (v : value) (s : sessnum),
    m_request_reply r v s → m_sequenced_client_request r v s

invariant [replica_sess_msg_num_eq_log_len]
  ∀ (r : replica) (s : sessnum), r_sess_msg_num r s ↔ r_log_len r s

#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true

#time #check_invariants

sat trace [replica_can_receive_request] {
  client_request
  replica_recv_sequenced_client_request
} by bmc_sat

sat trace [replica_can_receive_drop_notification] {
  client_request
  replica_recv_drop_notification
} by bmc_sat

sat trace [leader_can_receive_request] {
  client_request
  leader_recv_sequenced_client_request
} by bmc_sat

unsat trace [leader_cannot_reply_without_receiving_request] {
  client_request
  replica_recv_drop_notification
  leader_recv_slot_lookup_normal
} by bmc

sat trace [leader_can_reply_after_receiving_request] {
  client_request
  leader_recv_sequenced_client_request
  replica_recv_drop_notification
  leader_recv_slot_lookup_normal
} by bmc_sat

end NOPaxos
