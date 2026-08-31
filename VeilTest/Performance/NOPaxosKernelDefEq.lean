import Veil

veil module NOPaxos

type replica -- replica ID
enum replica_state = { st_normal, st_gap_commit }
type seq_t
type value
type quorum

instantiate seq : TotalOrderWithZero seq_t

immutable individual one : seq_t
immutable individual no_op : value
immutable individual leader : replica

immutable relation member (R : replica) (Q : quorum)

individual s_seq_msg_num : seq_t

relation r_log_len (r : replica) (i : seq_t)
relation r_log (r : replica) (i : seq_t) (v : value)
relation r_sess_msg_num (r : replica) (i : seq_t)
relation r_gap_commit_reps (r : replica) (p : replica)
relation r_current_gap_slot (r : replica) (i : seq_t)
relation r_replica_status (r : replica) (s : replica_state)

relation m_client_request (v : value)
relation m_marked_client_request  (dest : replica) (v : value) (sess_msg_num : seq_t)
relation m_request_reply (sender : replica) (request : value) (log_slot_num : seq_t)
relation m_slot_lookup (dest : replica) (sender : replica) (sess_msg_num : seq_t)
relation m_gap_commit (dest : replica) (slot_num : seq_t)
relation m_gap_commit_rep (dest : replica) (sender : replica) (slot_num : seq_t)

relation gh_r_received_sequenced_client_request (r : replica) (s : seq_t)
relation gh_r_received_drop_notification (r : replica) (s : seq_t)
relation gh_committed (s : seq_t) (v : value)

#gen_state

after_init {
  s_seq_msg_num := one;

  r_log_len R I := I == seq.zero
  r_log R I V := false
  r_sess_msg_num R I := I == one
  r_gap_commit_reps R P := false
  r_current_gap_slot R I := I == seq.zero
  r_replica_status R S := S == st_normal

  m_client_request V := false
  m_marked_client_request D V SMN := false
  m_request_reply S V LSN := false
  m_slot_lookup D S SMN := false
  m_gap_commit D SN := false
  m_gap_commit_rep D S SN := false

  gh_r_received_sequenced_client_request R S := false
  gh_r_received_drop_notification R S := false
  gh_committed S V := false
}

end NOPaxos
