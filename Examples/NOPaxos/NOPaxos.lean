import Veil

/-
  This is a simplified version of the NOPaxos protocol, without view
  changes. As such, the leader is modelled as fixed.
-/
veil module NOPaxos

type replica -- replica ID
enum leader_state = { st_normal, st_gap_commit }
type sessnum -- session number
type value
type quorum

instantiate seq : TotalOrderWithMinimum sessnum
immutable individual one : sessnum
immutable individual no_op : value
-- We don't model view changes, so the leader is fixed
immutable individual leader : replica

immutable relation member(R : replica) (Q : quorum)

-- Sequencer
-- the next session number to be assigned
individual s_sess_msg_num : sessnum

-- Replica
relation r_log (r : replica) (i : sessnum) (v : value)
relation r_log_len (r : replica) (i : sessnum)
-- the number of messages (requests or drop-notification) received by `r`
relation r_sess_msg_num (r : replica) (i : sessnum)

-- Leader gap commit state
individual leader_state : leader_state
individual leader_current_gap_slot : sessnum
-- set of replicas that the leader has received a gap commit response from
relation leader_gap_commit_reply (r : replica)

-- Network
-- message from the sequencer to the replicas with a sequenced client request
relation m_sequenced_client_request (dest : replica) (v : value) (s : sessnum)
-- message from a replica (or the leader) to the client with a request reply
relation m_request_reply (src : replica) (v : value) (s : sessnum)
-- replica `src` sends a slot lookup to the `leader` (implicit `dest`) for session number `s`
relation m_slot_lookup (src : replica) (s : sessnum)
-- leader replies to a slot lookup request from `dst` with a reply
relation m_slot_lookup_reply (dst : replica) (s : sessnum) (v : value)
-- leader sends a gap commit to `r` for session number `s`
relation m_gap_commit (r : replica) (s : sessnum)
-- replica `r` sends a gap commit reply to the leader for session number `s`
relation m_gap_commit_reply (r : replica) (s : sessnum)

-- Ghost state
relation gh_r_received_drop_notification (r : replica) (s : sessnum)
relation gh_committed (s : sessnum) (v : value)

#gen_state

assumption [zero_one] seq.next seq.zero one
assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : replica), member r q1 ∧ member r q2

-- FIXME: define these automatically (with a `partial function` keyword)
invariant [r_log_coherence] r_log R I V1 ∧ r_log R I V2 → V1 = V2
invariant [r_log_len_coherence] r_log_len R I1 ∧ r_log_len R I2 → I1 = I2
invariant [r_sess_msg_num_coherence] r_sess_msg_num R I1 ∧ r_sess_msg_num R I2 → I1 = I2

invariant [r_log_len_valid] r_log R I V ∧ r_log_len R L → seq.lt I L

after_init {
  s_sess_msg_num := seq.zero;

  r_log_len R I := I = seq.zero
  r_log R I V := False
  r_sess_msg_num R I := I = s_sess_msg_num

  m_sequenced_client_request R V S := False
  m_request_reply R V S := False

  leader_state := st_normal

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
  require leader_state = st_normal
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
  require m_slot_lookup mr mslot
  require leader_state = st_normal
  if len : r_log_len leader len then
    if smn : r_sess_msg_num leader smn then
      -- If we have a value for this slot, we reply to the slot lookup request
      require seq.lt mslot len
      if v : r_log leader mslot v then
        m_slot_lookup_reply mr mslot v := True
}

-- The leader enters the gap commit state and sends a gap commit to all
-- replicas, awaiting a quorum of replies.
procedure leader_send_gap_commit (logslot : sessnum) = {
  require leader_state = st_normal
  require r_log leader logslot no_op
  leader_state := st_gap_commit
  leader_gap_commit_reply R := False
  leader_current_gap_slot := logslot
  m_gap_commit R logslot := True
}

action leader_recv_drop_notification (mslot : sessnum) = {
  require m_slot_lookup leader mslot
  require leader_state = st_normal
  require ¬ gh_r_received_drop_notification leader mslot -- FIXME: we should be able to remove this
  gh_r_received_drop_notification leader mslot := True
  if logslot : r_log_len leader logslot then
    if smn : r_sess_msg_num leader smn then
      require smn = mslot -- we always process operations in order
      assert smn = logslot
      -- Insert a no-op into the log
      r_log leader logslot no_op := True
      let next_len ← succ logslot
      r_log_len leader I := I = next_len
      -- Send a gap commit to all replicas
      leader_send_gap_commit logslot
      -- In the TLA+ specification, the leader handles gap commit
      -- by reusing the `HandleGapCommit` transition. This somewhat
      -- obscures the logic, so we inline the transition here,
      -- special-cased for this (leader recv drop notification) situation.
      let next_smn ← succ smn
      r_sess_msg_num leader I := I = next_smn
      m_gap_commit_reply leader mslot := True
      m_request_reply leader no_op mslot := True
}

procedure replace_item_in_log (r : replica) (i : sessnum) (v : value) = {
  if len : r_log_len r len then
    require seq.le i len
    if i = len then
      let next_len ← succ len
      r_log_len r I := I = next_len
    r_log r i V := V = v
}

action replica_recv_gap_commit (r : replica) (mslot : sessnum) = {
  require r ≠ leader
  require m_gap_commit r mslot
  if logslot : r_log_len r logslot then
    if smn : r_sess_msg_num r smn then
      require seq.le mslot logslot -- we must have filled all log slots up to `mslot`
      replace_item_in_log r mslot no_op -- we put a no-op in the gap slot
      -- If the replica received a drop notification for `mslot`, it
      -- has to ignore the next request or drop-notification (but still
      -- increment its session number), to maintain consistency between its
      -- position in the OUM session and its log
      if gh_r_received_drop_notification r mslot then
        let next_smn ← succ smn
        r_sess_msg_num r I := I = next_smn
      m_gap_commit_reply r mslot := True
      m_request_reply r no_op mslot := True
}

action leader_recv_gap_commit_reply (mr : replica) (mslot : sessnum) = {
  require m_gap_commit_reply mr mslot
  require leader_state = st_gap_commit
  require leader_current_gap_slot = mslot
  leader_gap_commit_reply mr := True
  if ∃ (q:quorum), ∀ (p:replica), (member leader q ∧ member p q) → leader_gap_commit_reply mr then
    leader_state := st_normal
}

action client_commit (s : sessnum) (v : value) = {
  require ∃ (q:quorum), ∀ (p:replica), member p q → m_request_reply p v s
  gh_committed s v := True
}

invariant [no_spurious_sequencer_advance]
  ∀ (r : replica) (v : value) (s : sessnum),
    m_sequenced_client_request r v s → seq.lt s s_sess_msg_num

invariant [no_op_is_not_client_request]
  ∀ (r : replica) (v : value) (s : sessnum),
    m_sequenced_client_request r v s → v ≠ no_op

invariant [request_reply_implies_request_at_same_slot]
  ∀ (r : replica) (v : value) (s : sessnum),
    m_request_reply r v s → m_sequenced_client_request r v s

#time #gen_spec

end NOPaxos
