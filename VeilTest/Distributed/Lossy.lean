module

public import Veil

/-! Message loss in an asynchronous network, observed through deadlocks: the
pinger can never get stuck on a reliable network (proved), but it can on a
lossy one (found by bounded symbolic search). Also exercises `multiset`
channels. -/

veil module DistPingReliable

type node
immutable individual pinger : node

network (synchrony := async) (channels := multiset)

message ping
message pong

program (self : node) {
  if self = pinger then
    broadcast ping
    recv pong
  else
    recv ping from p
    send pong to p
}

-- without a second node, the pinger would wait for a pong forever
assumption [someone_else] ∃ n, n ≠ pinger

-- Until it is done, the pinger can make progress, or someone can answer it.
safety [no_deadlock]
  ¬ halted pinger →
    pc pinger = pc_start ∨
    ∃ n, n ≠ pinger ∧ ((ping_net pinger n > 0 ∧ pc n ≠ pc_done) ∨ pong_net n pinger > 0)

invariant [pinger_branch] pc pinger ≠ pc_recv1
invariant [other_branch] N ≠ pinger → pc N ≠ pc_recv2
invariant [ping_from_pinger] ping_net S D > 0 → S = pinger
invariant [one_copy] ping_net S D ≤ 1
invariant [pong_to_pinger] pong_net S D > 0 → D = pinger ∧ S ≠ pinger
invariant [before_start] pc pinger = pc_start → ping_net S D = 0 ∧ pc N ≠ pc_done
invariant [pinged_once] N ≠ pinger ∧ pc pinger ≠ pc_start → (ping_net pinger N > 0 ↔ pc N ≠ pc_done)
invariant [answered] N ≠ pinger ∧ pc N = pc_done ∧ ¬ halted pinger → pong_net N pinger > 0

#gen_spec

#check_invariants

end DistPingReliable

veil module DistPingLossy

type node
immutable individual pinger : node

network (synchrony := async) (loss := lossy)

message ping
message pong

program (self : node) {
  if self = pinger then
    broadcast ping
    recv pong
  else
    recv ping from p
    send pong to p
}

/-- warning: you have not defined any invariants or temporal properties for this specification; did you forget? -/
#guard_msgs in
#gen_spec

-- the pinger waits for a pong that will never come
sat trace [stuck] {
  any 4 actions
  assert (pc pinger = pc_recv2 ∧ ∀ s d, ping_net s d = false ∧ pong_net s d = false)
}

end DistPingLossy
