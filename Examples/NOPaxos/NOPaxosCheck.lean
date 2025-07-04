import Examples.NOPaxos.NOPaxos

veil module NOPaxos

set_option maxHeartbeats 0
-- set_option veil.smt.model.minimize true

unsat trace [cannot_sequence_two_values_at_same_slot] {
  client_request
  client_request
  assert (∃ (r r' : replica) (mslot : sessnum) (v v' : value),
    m_sequenced_client_request r v mslot ∧
    m_sequenced_client_request r' v' mslot ∧
    v ≠ v')
} by bmc

unsat trace [cannot_receive_request_then_drop_in_same_slot] {
  client_request
  replica_recv_sequenced_client_request
  replica_recv_drop_notification
  assert (∃ r mslot, gh_r_received_drop_notification r mslot ∧ gh_r_received_sequenced_client_request r mslot)
} by bmc

unsat trace [cannot_drop_then_receive_request_in_same_slot] {
  client_request
  replica_recv_drop_notification
  replica_recv_sequenced_client_request
  assert (∃ r mslot, gh_r_received_drop_notification r mslot ∧ gh_r_received_sequenced_client_request r mslot)
} by bmc

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

sat trace [leader_can_send_gap_commit] {
  client_request
  leader_recv_drop_notification
  assert (leader_state = leader_state_Enum.st_gap_commit)
} by bmc_sat

sat trace [replica_overwrites_received_slot] {
  assert (∃ (r₁ r₂ : replica), r₁ ≠ r₂ ∧ ∀ r, r = r₁ ∨ r = r₂)
  client_request
  replica_recv_sequenced_client_request
  assert (∃ r mslot v, r ≠ leader ∧ v ≠ no_op ∧ r_log r mslot v)
  leader_recv_drop_notification
  assert (leader_state = leader_state_Enum.st_gap_commit)
  replica_recv_gap_commit
  assert (∃ r mslot, m_gap_commit_reply r mslot ∧ r_log r mslot no_op)
} by bmc_sat

unsat trace [replica_with_gap_commit_ignores_next_request] {
  assert (∃ (r₁ r₂ : replica), r₁ ≠ r₂ ∧ ∀ r, r = r₁ ∨ r = r₂)
  client_request
  replica_recv_drop_notification
  assert (∃ r mslot, gh_r_received_drop_notification r mslot)
  leader_recv_drop_notification
  assert (leader_state = leader_state_Enum.st_gap_commit)
  replica_recv_gap_commit
  replica_recv_sequenced_client_request
} by bmc

sat trace [client_can_commit_normal] {
  client_request
  replica_recv_sequenced_client_request
  leader_recv_sequenced_client_request
  client_commit
} by bmc_sat

sat trace [client_can_commit_gap_commit] {
  -- assert (∃ (r₁ r₂ r₃ : replica), (distinct r₁ r₂ r₃) ∧ (∀ r, r = r₁ ∨ r = r₂ ∨ r = r₃)
    -- ∧ (∃ (q : quorum), (∃ (r₁ r₂ :replica), r₁ ≠ r₂ ∧ memb–er r₁ q ∧ member r₂ q)))
  client_request
  replica_recv_sequenced_client_request
  leader_recv_drop_notification
  assert (leader_state = leader_state_Enum.st_gap_commit)
  replica_recv_gap_commit
  client_commit
} by bmc_sat

sat trace [can_commit_twice] {
  any 6 actions
  client_commit
  client_commit
} by bmc_sat


-- FIXME: why is this possible!?
set_option veil.smt.timeout 300
unsat trace [cannot_commit_inconsistently] {
  any 6 actions
  client_commit
  client_commit
  assert (∃ s v v', gh_committed s v ∧ gh_committed s v' ∧ v ≠ v')
} by bmc

end NOPaxos
