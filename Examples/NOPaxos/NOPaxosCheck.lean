import Examples.NOPaxos.NOPaxos

veil module NOPaxos

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true

-- #time #check_invariants
-- #time #check_action leader_recv_drop_notification


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

end NOPaxos
