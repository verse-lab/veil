import Veil

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

individual s_seq_msg_num : seq_t

-- Replica
relation r_log_len (r : replica) (i : seq_t)
relation r_log (r : replica) (i : seq_t) (v : value)
relation r_sess_msg_num (r : replica) (i : seq_t)   -- the expected _next_ message number
relation r_gap_commit_reps (r : replica) (p : replica)
relation r_current_gap_slot (r : replica) (i : seq_t)
relation r_replica_status (r : replica) (s : replica_state)

-- -- Network
relation m_client_request (v : value)
relation m_marked_client_request  (dest : replica) (v : value) (sess_msg_num : seq_t)
relation m_request_reply (sender : replica) (request : value) (log_slot_num : seq_t)
relation m_slot_lookup (dest : replica) (sender : replica) (sess_msg_num : seq_t)
relation m_gap_commit (dest : replica) (slot_num : seq_t)
relation m_gap_commit_rep (dest : replica) (sender : replica) (slot_num : seq_t)

-- -- Ghost state
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
  pure ()
}

procedure succ (n : seq_t) {
  let k :| next n k
  return k
}

procedure send_gap_commit (r : replica) {
  require r = leader
  require r_replica_status r st_normal
  let len :| r_log_len r len
  let slot ← succ len
  r_replica_status r S := S == st_gap_commit
  r_gap_commit_reps r P := false
  r_current_gap_slot r I := I == slot
  m_gap_commit R slot := true
}

action handle_slot_lookup (r : replica) (m_sender : replica) (m_sess_msg_num : seq_t) {
  require m_slot_lookup r m_sender m_sess_msg_num
  require r_replica_status r st_normal
  require r = leader
  let len :| r_log_len r len
  let smn :| r_sess_msg_num r smn
  let slot := m_sess_msg_num
  if seq.le slot len then
    if v : r_log r slot v then
      m_marked_client_request m_sender v m_sess_msg_num := true
    else
      pure ()
  if slot = (← succ len) then
    send_gap_commit r
}

-- NOTE: The thing to notice is that `handle_slot_lookup` contains
-- two `Decidable` instance arguments with the same type, and we need to
-- ensure that this will not trigger weird instance synthesis problem

invariant [inv] True

set_option maxHeartbeats 10000000
#gen_spec

end NOPaxos
