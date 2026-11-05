module

public import Veil

veil module DistPingPong

type node
type value
immutable individual pinger : node
immutable individual payload : value

network (synchrony := async) (complexity := true)

message ping (v : value)
message pong (v : value)

var reply : value := *
var served : Nat := 0

program (self : node) {
  if self = pinger then
    let other :| other ≠ self
    send (ping payload) to other
    recv (pong v) from _src
    reply := v
  else
    recv (ping v) from src
    served := served + 1
    send (pong v) to src
}

safety [pinger_gets_payload] halted pinger → reply pinger = payload
safety [two_messages] net_msgs ≤ 2
-- The pinger can always make progress until it is done: it has not started,
-- or there is a message in flight that someone can receive.
safety [no_deadlock]
  ¬ halted pinger →
    pc pinger = pc_start ∨ (∃ s d v, ping_net s d v) ∨ (∃ s d v, pong_net s d v)

invariant [ping_from_pinger] ping_net S D V → S = pinger ∧ V = payload ∧ D ≠ pinger
invariant [pong_to_pinger] pong_net S D V → D = pinger ∧ V = payload
invariant [one_ping] ping_net S D V ∧ ping_net S2 D2 V2 → D = D2
invariant [one_pong] pong_net S D V ∧ pong_net S2 D2 V2 → S = S2
invariant [replied_after_ping]
  N ≠ pinger ∧ pc N = pc_done → pc pinger ≠ pc_start ∧ ping_net S D V = false
invariant [ping_receiver_waits] ping_net S D V → pc D ≠ pc_done
invariant [ping_waiting] ping_net S D V → pc pinger = pc_recv2
invariant [before_start]
  pc pinger = pc_start → net_msgs = 0 ∧ ping_net S D V = false ∧ pong_net S D V = false
invariant [ping_phase] ping_net S D V → net_msgs = 1 ∧ pong_net S2 D2 V2 = false
invariant [pong_phase] pong_net S D V → net_msgs = 2 ∧ pc pinger = pc_recv2
invariant [ping_consumed]
  pc pinger ≠ pc_start ∧ (∀ s d v, ping_net s d v = false) → net_msgs = 2

#gen_spec

#check_invariants

end DistPingPong
