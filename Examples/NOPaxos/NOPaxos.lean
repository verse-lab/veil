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
relation gh_what_status_when_replying (r : replica) (s : seq_t) (status : replica_state)
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
  gh_what_status_when_replying R S SS := False
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
    r_log r i V := V = v
}

action client_sends_request (v : value) = {
  require v ≠ no_op
  m_client_request v := True
}

-- Sequencer handles the client request
action handle_client_request (m_value : value) = {
  require m_client_request m_value
  let slot := s_seq_msg_num
  m_marked_client_request R m_value slot := True
  let next_slot ← succ slot
  s_seq_msg_num := next_slot
}

procedure append_to_log (r : replica) (v : value) = {
  let len :| r_log_len r len
  -- TLA arrays are 1-indexed, so we replicate this here
  -- if len = seq.zero then
  --   r_log r seq.zero no_op := True
  --   r_log r one v := True
  -- else
  --   r_log r len v := True
  let next_len ← succ len
  r_log r next_len v := True
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
  -- let len :| r_log_len r len
  let smn :| r_sess_msg_num r smn
  require m_sess_msg_num = smn
  gh_r_received_sequenced_client_request r m_sess_msg_num := True
  let _new_smn ← increase_session_number r
  let new_len ← append_to_log r m_value
  gh_what_status_when_replying r new_len st_normal := True
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
  m_gap_commit R slot := True
}

-- Drop notification case of `HandleMarkedClientRequest`
action handle_marked_client_drop_notification (r : replica) (m_value : value) (m_sess_msg_num : seq_t) = {
  require m_marked_client_request r m_value m_sess_msg_num
  require r_replica_status r st_normal
  let smn :| r_sess_msg_num r smn
  -- NOTE: this is the condition in the TLA+ spec, but it means that
  -- a drop notification cannot be sent for the first session number,
  -- which seems incorrect.
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
  -- (i.e., with no view changes, we should have `vSessMsgNum[r]` = `Len(vLog[r]) + 1`)
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

-- Replica r (or the leader) receives GapCommit
action handle_gap_commit (r : replica) (m_slot_num : seq_t) = {
  require m_gap_commit r m_slot_num
  -- require r_replica_status r st_normal ∨ r_replica_status r st_gap_commit
  let len :| r_log_len r len
  -- NOTE: this condition ensures that the skipping operation (the `if` block
  -- below) is meaningful, or intuitively "not too early"
  require seq.le m_slot_num len ∨ next seq_t len m_slot_num
  let smn :| r_sess_msg_num r smn
  replace_item r m_slot_num no_op
  if lt seq_t len m_slot_num then
    let  _new_smn ← increase_session_number r
  m_gap_commit_rep leader r m_slot_num := True
  let st :| r_replica_status r st
  gh_what_status_when_replying r m_slot_num st := True
  m_request_reply r no_op m_slot_num := True
}

action handle_gap_commit_rep (r : replica) (m_sender : replica) (m_slot_num : seq_t) = {
  require m_gap_commit_rep r m_sender m_slot_num
  require r_replica_status r st_gap_commit
  require r = leader
  require r_current_gap_slot r m_slot_num
  r_gap_commit_reps r m_sender := True
  if (r_gap_commit_reps r r) ∧ (∃ (q:quorum), ∀ (p:replica),
    member p q → r_gap_commit_reps r p) then
    r_replica_status r S := S = st_normal
}

action client_commit (s : seq_t) (v : value) = {
  require ∃ (q:quorum), ∀ (p:replica), member p q → m_request_reply p v s
  require m_request_reply leader v s
  gh_committed s v := True
}

-- invariants for functions (implemented as partial functions)
invariant [ll_coherence] (r_log_len R I1 ∧ r_log_len R I2) → I1 = I2
invariant [log_coherence] (r_log R I V1 ∧ r_log R I V2) → V1 = V2
invariant [smn_coherence] (r_sess_msg_num R I1 ∧ r_sess_msg_num R I2) → I1 = I2
invariant [cgs_coherence] (r_current_gap_slot R I1 ∧ r_current_gap_slot R I2) → I1 = I2
invariant [status_coherence] (r_replica_status R S1 ∧ r_replica_status R S2) → S1 = S2

-- sanity check
invariant [leader_status_either] r_replica_status leader st_normal ∨ r_replica_status leader st_gap_commit
invariant [only_leader_can_gap_status] r_replica_status R st_gap_commit → R = leader
invariant [client_no_op] ¬ m_client_request no_op

-- relations between `r_log`, `r_log_len`, `r_sess_msg_num`, `s_seq_msg_num`
invariant [log_valid_1] (r_log R I V ∧ r_log_len R L) → seq.le I L

-- NOTE: weaker than `valid_sess_msg_num`
invariant [log_smn] (r_sess_msg_num R I ∧ seq.le I J) → ¬ r_log R J V
invariant [valid_sess_msg_num] (r_log_len R I ∧ r_sess_msg_num R J) → next seq_t I J

-- to prove consistency, it suffices to show that the leader never rolls back
-- by sending two different replies for the same request
invariant [gh_committed_cause] gh_committed S V → m_request_reply leader V S
invariant [leader_never_rolls_back] (m_request_reply leader V1 S ∧ m_request_reply leader V2 S) → V1 = V2
safety [consistency] gh_committed S V1 ∧ gh_committed S V2 → V1 = V2

-- we can know the source of the request reply
-- note that, to show the first disjunct, we need `valid_sess_msg_num`
invariant [m_request_reply_source] (m_request_reply R V S) → (m_marked_client_request R V S ∨ (V = no_op ∧ m_gap_commit R S))

-- if `V1` and `V2` come from `gap_commit`, then they are both `no_op`, so fine

-- if `V1` and `V2` come from `m_marked_client_request`, then we show that values
-- from `m_marked_client_request` are essentially unique _for the leader_
-- we can show this by searching for the possible sources of `marked_client_request`
invariant [lookup_by_non_leader] m_slot_lookup R P S → P ≠ leader
invariant [marked_request_for_leader_unique] m_marked_client_request leader V1 S ∧ m_marked_client_request leader V2 S → V1 = V2
invariant [m_marked_client_request_bounded] m_marked_client_request R V S → lt seq_t S s_seq_msg_num
invariant [m_marked_client_request_source] m_marked_client_request R V S → m_slot_lookup leader R S ∨ m_client_request V
invariant [m_slot_lookup_bounded] m_slot_lookup P R S → lt seq_t S s_seq_msg_num

-- otherwise, we show that it is impossible for the leader to reply through
-- the two different sources

invariant [log_smn_gap] (m_gap_commit R S ∧ r_sess_msg_num leader I) → seq.le S I
-- invariant [log_smn_gap_2] (m_gap_commit R S ∧ r_log_len leader I) → (seq.le S I ∨ next seq_t I S)
invariant [lead_gap_commits] (r_log_len leader I ∧ seq.le J I ∧ m_gap_commit R J) → r_log leader J no_op
invariant [leader_reply_matches_log] (m_request_reply leader V I) → r_log leader I V
invariant [log_smn_gap_normal] (m_gap_commit R S ∧ r_log_len leader I ∧ r_replica_status leader st_normal) → seq.le S I
-- invariant [r_gap_commit_reps_source] r_gap_commit_reps R P → ∃ (s : seq_t), m_gap_commit_rep R P s

-- invariant [r_gap_commit_reps_leader_only] r_gap_commit_reps R P → R = leader
invariant [m_gap_commit_rep_to_leader_only] m_gap_commit_rep R P S → R = leader

-- invariant [m_gap_commit_rep_source] m_gap_commit_rep R P S → m_gap_commit P S
invariant [r_gap_commit_reps_source] (r_replica_status leader st_gap_commit ∧ r_current_gap_slot leader I ∧ r_gap_commit_reps leader P) → m_gap_commit_rep leader P I
invariant [m_gap_commit_rep_len] (m_gap_commit_rep R P S ∧ r_log_len P I) → seq.le S I
-- invariant [leader_smn_gap_status] (r_replica_status leader st_gap_commit ∧ r_current_gap_slot leader I ∧ r_log_len leader I2) → seq.le I I2 ∨ next seq_t I2 I
invariant [m_gap_commit_slot] (r_replica_status leader st_gap_commit ∧ m_gap_commit R S ∧ r_current_gap_slot leader I) → seq.le S I
#time #gen_spec

-- set_option veil.printCounterexamples true
-- set_option veil.smt.model.minimize true
#time #check_invariants

-- set_option veil.smt.model.minimize true
set_option maxHeartbeats 0

/-
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


sat trace [r_ses_number_increases] {
  client_sends_request
  handle_client_request
  assert (∃ (r : replica) (v : value) (s : seq_t), m_marked_client_request r v one)
  handle_marked_client_request_normal
  assert (∃ (r : replica), r_sess_msg_num r one)
} by bmc_sat

sat trace [can_get_dropped] {
  assert (∃ (r₁ r₂ : replica), r₁ ≠ r₂ ∧ ∀ r, r = r₁ ∨ r = r₂)
  client_sends_request
  handle_client_request
  assert (∃ (r : replica) (v : value) (s : seq_t), m_marked_client_request r v one)
  handle_marked_client_request_normal
  client_sends_request
  handle_client_request
  handle_marked_client_drop_notification
  -- handle_slot_lookup
} by bmc_sat

sat trace [leader_can_handle_gap_commit] {
  client_sends_request
  handle_client_request
  handle_marked_client_request_normal
  client_sends_request
  handle_client_request
  handle_marked_client_drop_notification
  assert (∃ (r : replica) (s : seq_t), gh_r_received_drop_notification leader s)
  handle_gap_commit
} by bmc_sat

sat trace [leader_can_handle_gap_commit_rep] {
  client_sends_request
  handle_client_request
  handle_marked_client_request_normal
  client_sends_request
  handle_client_request
  handle_marked_client_drop_notification
  assert (∃ (r : replica) (s : seq_t), gh_r_received_drop_notification leader s)
  handle_gap_commit
  handle_gap_commit_rep
} by bmc_sat
-/

-- sat trace [can_commit] {
--   any 4 actions
--   client_commit
--   assert (∃ (s : seq_t) (v : value), gh_committed s v)
-- } by bmc_sat

-- #time #check_invariants
set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
-- #time #check_action replica_recv_sequenced_client_request
-- #time #check_invariants!
-- #time #check_action replica_recv_gap_commit

end NOPaxos
