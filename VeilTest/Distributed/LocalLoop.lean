module

public import Veil

/-! A loop that never blocks (each iteration is a step of its own, resumed at
the loop head), followed by one that blocks on every iteration. -/

veil module DistLocalLoop

type node
immutable individual pinger : node

network (synchrony := async)

message ping
message pong

var asked : node → Bool := fun _ => false
var answered : node → Bool := fun _ => false

program (self : node) {
  if self = pinger then
    while ∃ n, n ≠ self ∧ ¬ asked n do
      let n :| n ≠ self ∧ ¬ asked n
      asked n := true
      send ping to n
    while ∃ n, n ≠ self ∧ ¬ answered n do
      recv pong from p
      answered p := true
  else
    recv ping from p
    send pong to p
}

safety [all_answered] halted pinger → ∀ n, n ≠ pinger → answered pinger n
-- Until it is done, the pinger can always make progress: it is still sending,
-- or there is a message in flight that someone can receive.
safety [no_deadlock]
  ¬ halted pinger →
    pc pinger = pc_start ∨ pc pinger = pc_loop2 ∨ (∃ d, ping_net pinger d) ∨ (∃ s, pong_net s pinger)

-- the pinger and the others run different branches
invariant [pinger_branch] pc pinger ≠ pc_recv1
invariant [other_branch] N ≠ pinger → pc N ≠ pc_loop2 ∧ pc N ≠ pc_recv4
-- each node is pinged once, and answers once
invariant [ping_asked] ping_net S D → S = pinger ∧ D ≠ pinger ∧ asked pinger D
invariant [pong_to_pinger] pong_net S D → D = pinger ∧ S ≠ pinger
invariant [pinged_waits] ping_net pinger N → pc N ≠ pc_done
invariant [done_was_asked] N ≠ pinger ∧ pc N = pc_done → asked pinger N ∧ ping_net pinger N = false
invariant [pong_after_done] pong_net N pinger → pc N = pc_done
invariant [answered_asked] answered pinger N → N ≠ pinger ∧ asked pinger N
-- every asked node is still pinged, answering, or answered
invariant [tracked]
  N ≠ pinger ∧ asked pinger N ∧ ¬ answered pinger N → ping_net pinger N ∨ pong_net N pinger
-- the receiving loop starts after everyone is asked, and runs while someone has not answered
invariant [asked_all]
  pc pinger = pc_recv4 ∨ halted pinger → ∀ n, n ≠ pinger → asked pinger n
invariant [waiting_for_someone] pc pinger = pc_recv4 → ∃ n, n ≠ pinger ∧ ¬ answered pinger n

#gen_spec

#check_invariants

end DistLocalLoop
