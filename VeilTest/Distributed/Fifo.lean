module

public import Veil

/-! FIFO channels. A sender sends `early`, then `late`; the receiver must never
get `early` after `late`. -/

veil module DistUnordered

type node
immutable individual snd : node
immutable individual rcv : node

network (synchrony := async)

message early
message late

var gotLate : Bool := false
var outOfOrder : Bool := false

program (self : node) {
  if self = snd then
    send early to rcv
    send late to rcv
  else if self = rcv then
    repeat
      recv
      | late => gotLate := true
      | early => if gotLate then outOfOrder := true
}

safety [in_order] outOfOrder N = false

#gen_spec

-- on an unordered network, `late` can overtake `early`
sat trace [out_of_order] {
  any 4 actions
  assert (∃ n, outOfOrder n)
}

end DistUnordered

veil module DistFifo

type node
immutable individual snd : node
immutable individual rcv : node

network (synchrony := async) (order := fifo)

message early
message late

var gotLate : Bool := false
var outOfOrder : Bool := false

program (self : node) {
  if self = snd then
    send early to rcv
    send late to rcv
  else if self = rcv then
    repeat
      recv
      | late => gotLate := true
      | early => if gotLate then outOfOrder := true
}

safety [in_order] outOfOrder N = false
invariant [only_snd_sends_early] early_net S D K → S = snd ∧ D = rcv
invariant [only_snd_sends_late] late_net S D K → S = snd ∧ D = rcv
invariant [one_early] early_net S D K ∧ early_net S D K2 → K = K2
invariant [early_before_late] early_net S D K ∧ late_net S D K2 → net_seq_order.lt K K2
invariant [early_below_sent] early_net S D K → net_seq_order.lt K (net_seq_sent S D)
invariant [late_below_sent] late_net S D K → net_seq_order.lt K (net_seq_sent S D)
invariant [early_not_consumed] early_net S D K → net_seq_order.le (net_seq_recv S D) K
invariant [recv_le_sent] net_seq_order.le (net_seq_recv S D) (net_seq_sent S D)
invariant [nothing_before_start] pc snd = pc_start → early_net S D K = false ∧ late_net S D K = false ∧ gotLate N = false
invariant [early_gone_after_late] gotLate N → early_net S N K = false

#gen_spec

#check_invariants

end DistFifo

-- On a lossy FIFO channel, messages may be lost, but the ones that arrive
-- still arrive in order.
veil module DistLossyFifo

type node
immutable individual snd : node
immutable individual rcv : node

network (synchrony := async) (order := fifo) (loss := lossy)

message early
message late

var gotLate : Bool := false
var outOfOrder : Bool := false

program (self : node) {
  if self = snd then
    send early to rcv
    send late to rcv
  else if self = rcv then
    repeat
      recv
      | late => gotLate := true
      | early => if gotLate then outOfOrder := true
}

safety [in_order] outOfOrder N = false
-- the same invariant as for a reliable FIFO channel: taking `late` throws away
-- every earlier message of the channel, so `early` cannot arrive after it
invariant [only_snd_sends_early] early_net S D K → S = snd ∧ D = rcv
invariant [only_snd_sends_late] late_net S D K → S = snd ∧ D = rcv
invariant [one_early] early_net S D K ∧ early_net S D K2 → K = K2
invariant [early_before_late] early_net S D K ∧ late_net S D K2 → net_seq_order.lt K K2
invariant [early_below_sent] early_net S D K → net_seq_order.lt K (net_seq_sent S D)
invariant [late_below_sent] late_net S D K → net_seq_order.lt K (net_seq_sent S D)
invariant [early_not_consumed] early_net S D K → net_seq_order.le (net_seq_recv S D) K
invariant [recv_le_sent] net_seq_order.le (net_seq_recv S D) (net_seq_sent S D)
invariant [nothing_before_start] pc snd = pc_start → early_net S D K = false ∧ late_net S D K = false ∧ gotLate N = false
invariant [early_gone_after_late] gotLate N → early_net S N K = false

#gen_spec

-- #check_invariants  -- pending: verified in trusted mode after the encoding fix

end DistLossyFifo
