import Veil

-- https://github.com/markyuen/tlaplus-to-ivy/blob/845b4e5d00dc5540cc058b50b910c379523e538c/ivy/nopaxos.ivy

veil module NOPaxos

enum r_state = { st_normal, st_gap_commit, st_view_change }
type quorum
type value
type seq_t
type replica

-- Sequencer
relation s_seq_msg_num (s : seq_t) (i : seq_t)

-- Replica
relation r_log_len (r : replica) (i : seq_t)
relation r_log (r : replica) (i : seq_t) (v : value)
relation r_sess_msg_num (r : replica) (i : seq_t)
relation r_gap_commit_reps (r : replica) (p : replica)
relation r_current_gap_slot (r : replica) (i : seq_t)
relation r_replica_status (r : replica) (s : r_state)

-- Network
relation m_client_request (v : value)
relation m_marked_client_request (dest : replica) (v : value) (sessMsgNum : seq_t)
relation m_request_reply (sender : replica) (request : value) (logSlotNum : seq_t)
relation m_slot_lookup (dest : replica) (sender : replica) (sessMsgNum : seq_t)
relation m_gap_commit (dest : replica) (slotNum : seq_t)
relation m_gap_commit_rep (dest : replica) (sender : replica) (slotNum : seq_t)

-- Helpers
immutable relation member (r : replica) (q : quorum)
immutable relation leader (r : replica)

individual no_op : value
individual sequencer : seq_t
immutable individual one : seq_t
immutable individual lead : replica

instantiate seq : TotalOrderWithMinimum seq_t

#gen_state

assumption [r_state_enum] ∀ (rs : r_state), (rs = st_normal ∨ rs = st_gap_commit ∨ rs = st_view_change)
assumption [r_state_distinct] (st_normal ≠ st_gap_commit) ∧ (st_normal ≠ st_view_change) ∧ (st_gap_commit ≠ st_view_change)

assumption [zero_one] seq.next seq.zero one
assumption [quorum_intersection] ∀ (q₁: quorum) (q₂: quorum), ∃ (r: replica), member r q₁ ∧ member r q₂
assumption [single_leader] ∀ (R : replica), leader R ↔ R = lead

after_init {
  s_seq_msg_num S I := S = sequencer ∧ I = one;

  r_log_len R I := I = seq.zero;
  r_log R I V := False;
  r_sess_msg_num R I := I = one;
  r_gap_commit_reps R P := False;
  r_current_gap_slot R I := I = seq.zero;
  r_replica_status R S := S = st_normal;

  m_client_request V := False;
  m_marked_client_request D V SMN := False;
  m_request_reply S V LSN := False;
  m_slot_lookup D S SMN := False;
  m_gap_commit D SN := False;
  m_gap_commit_rep D S SN := False
}

-- Internal procedures
procedure succ(n : seq_t) = {
  let k ← pick seq_t
  assume seq.next n k
  return k
}

procedure replace_item (r : replica) (i : seq_t) (v : value) = {
  if len : (r_log_len r len) then
    if (seq.le i (← succ len)) then
      if i = (← succ len) then
        r_log_len r I := I = i
    r_log r i V := V = v
}

procedure send_gap_commit (r : replica) = {
  if len : (r_log_len r len) then
    assert leader r; -- ensure leader r
    assert r_replica_status r st_normal -- ensure r_replica_status r r_state.st_normal;
    let slot ← succ len
    r_replica_status r S := S = st_gap_commit
    r_gap_commit_reps r P := False
    r_current_gap_slot r I := I = slot
    m_gap_commit R slot := True
}

-- Transitions
action client_send_request (v : value) = {
  require v ≠ no_op
  m_client_request v := True
}

action handle_client_request (m_value : value) (s : seq_t) = {
  require s = sequencer
  require m_client_request m_value
  if slot : (s_seq_msg_num s slot) then
    m_marked_client_request R m_value slot := True
    let k ← succ slot
    s_seq_msg_num s I := I = k
}

action handle_marked_client_request (r : replica) (m_value : value) (m_sess_msg_num : seq_t) = {
  require m_marked_client_request r m_value m_sess_msg_num
  if len : (r_log_len r len) then
    if smn : (r_sess_msg_num r smn) then
      require r_replica_status r st_normal
      if m_sess_msg_num = smn then
        r_log_len r I := I = smn
        r_log r smn m_value := True
        let k ← succ smn
        r_sess_msg_num r I := I = k
        m_request_reply r m_value smn := True
      -- Note: we ignore the session terminated case
      if seq.lt smn m_sess_msg_num then
        if leader r then
          send_gap_commit r
        else
          m_slot_lookup lead r smn := True
}

action handle_slot_lookup (r : replica) (m_sender : replica) (m_sess_msg_num : seq_t) = {
  require m_slot_lookup r m_sender m_sess_msg_num
  if len : (r_log_len r len) then
    -- Note: in TLA+ the slot is computed as `logSlotNum ==
    -- Len(vLog[r]) + 1 - (vSessMsgNum[r] - m.sessMsgNum)` which
    -- calculates the offset from the tail of the log; however, with
    -- no view changes, this is equivalent to simply taking the index
    -- of the incoming `m.sessMsgNum`
    let slot := m_sess_msg_num
    require leader r
    require r_replica_status r st_normal
    if seq.le slot len then
      if v : r_log r slot v then
        m_marked_client_request m_sender v m_sess_msg_num := True
      else
        -- Nothing to undo
        pure ()
    if slot = (← succ len)then
      send_gap_commit r
}

action handle_gap_commit (r : replica) (m_slot_num : seq_t) = {
  require m_gap_commit r m_slot_num
  if len : (r_log_len r len) then
    if smn : (r_sess_msg_num r smn) then
      require seq.le m_slot_num (← succ len)
      require r_replica_status r st_normal ∨ r_replica_status r st_gap_commit
      replace_item r m_slot_num no_op
      if seq.lt len m_slot_num then
        let m ← succ smn
        r_sess_msg_num r I := I = m
      m_gap_commit_rep lead r m_slot_num := True
      m_request_reply r no_op m_slot_num := True
}

action hangle_gap_commit_rep (r : replica) (m_sender : replica) (m_slot_num : seq_t) = {
  -- (*) Not part of the original protocol -- this is added simply to make writing
  -- the inductive invariant easier. This condition always holds in an actual
  -- execution before the replica status can be returned to normal. The reason
  -- why is because for the recipient -- the leader -- to be part of the quorum,
  -- it must have gone through the handle_gap_commit handler, incrementing its
  -- sess msg num beyond the current gap slot. This condition is extracted to
  -- this `before` construct simply for clarity -- there is no real operational
  -- difference in this placement.
  require ∀ i, r_sess_msg_num r i ∧ seq.lt m_slot_num i
  -- Actual transition starts here:
  require m_gap_commit_rep r m_sender m_slot_num
  require r_replica_status r st_gap_commit
  require leader r
  require r_current_gap_slot r m_slot_num
  r_gap_commit_reps r m_sender := True
  if ∃ (q:quorum), ∀ (p:replica), member r q ∧ member p q → r_gap_commit_reps r p then
    r_replica_status r S := S = st_normal
}

invariant [sequencer_coherence] (s_seq_msg_num S I1 ∧ s_seq_msg_num S I2) → I1 = I2
invariant [ll_coherence] (r_log_len R I1 ∧ r_log_len R I2) → I1 = I2
invariant [log_coherence] (r_log R I V1 ∧ r_log R I V2) → V1 = V2
invariant [smn_coherence] (r_sess_msg_num R I1 ∧ r_sess_msg_num R I2) → I1 = I2
invariant [cgs_coherence] (r_current_gap_slot R I1 ∧ r_current_gap_slot R I2) → I1 = I2
invariant [status_coherence] (r_replica_status R S1 ∧ r_replica_status R S2) → S1 = S2

invariant [single_sequencer_1] (S = sequencer ∧ s_seq_msg_num sequencer I) → seq.le one I
invariant [single_sequencer_2] S ≠ sequencer → ¬ s_seq_msg_num S I

invariant [log_valid_1] (r_log R I V ∧ r_log_len R L) → seq.le I L
-- invariant [log_valid_2] (r_log_len R I ∧ seq.le J I) → ∃ v, r_log R J v -- (commented out in source)

invariant [leader_reply_matches_log] (leader R ∧ m_request_reply R V I) → r_log R I V

invariant [client_no_op] ¬ m_client_request no_op

invariant [marked_req_non_trivial] (V ≠ no_op ∧ m_marked_client_request R V I) → m_client_request V

invariant [request_reply_non_trivial] (V ≠ no_op ∧ m_request_reply R V I) → m_client_request V

invariant [log_non_trivial] (V ≠ no_op ∧ r_log R I V) → m_marked_client_request R V I

invariant [valid_sess_msg_num] (r_log_len R I ∧ r_sess_msg_num R J) → seq.next I J

invariant [lead_gap_commits] (leader R ∧ r_log_len R I ∧ seq.le J I) → (¬ m_gap_commit R J ∨ r_log R J no_op)

invariant [log_smn] (r_sess_msg_num R I ∧ seq.le I J) → ¬ r_log R J V

invariant [log_smn_gap] (leader R ∧ r_sess_msg_num R I ∧ seq.lt I J) → ¬ m_gap_commit R J

invariant [reply_smn] (m_request_reply R V I ∧ r_sess_msg_num R J) → seq.lt I J

invariant [leader_smn_gap] (leader R ∧ r_sess_msg_num R I ∧ m_gap_commit R I ∧ m_gap_commit R J ∧ seq.le J I)
    → (r_replica_status R st_gap_commit ∧ r_current_gap_slot R I)

safety [consistency] ((∃ (q: quorum), member lead q ∧ ∀ (r : replica), member r q → m_request_reply r V1 I) ∧
                (∃ (q: quorum), member lead q ∧ ∀ (r : replica), member r q → m_request_reply r V2 I))
                → V1 = V2
#gen_spec

set_option maxHeartbeats 0

-- set_option veil.smt.translator "lean-smt"
-- set_option veil.smt.reconstructProofs true

#time #check_invariants!

sat trace { } by bmc_sat

end NOPaxos
