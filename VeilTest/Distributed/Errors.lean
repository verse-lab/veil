module

public import Veil

/-! The compiler's checks: what a node program may not do. -/

veil module DistErrSharedState
type node
relation shared : node → Bool
network
var x : Bool := false
/--
error: `shared` is shared state, which a node program cannot access: a node can only use its own `var`s, and communicate with `send` and `recv`
-/
#guard_msgs in
program (self : node) {
  x := shared self
}
end DistErrSharedState

veil module DistErrOtherNode
type node
network
var x : Bool := false
/--
error: `x` takes 0 argument(s): it is this node's own variable, and a node cannot read another node's copy (in a `program`, `x` means `x self`)
-/
#guard_msgs in
program (self : node) {
  let other :| other ≠ self
  x := x other
}
end DistErrOtherNode

veil module DistErrGenerated
type node
network
/--
error: a node program cannot access `pc`: it is part of the network and scheduler state that `program` generates
-/
#guard_msgs in
program (self : node) {
  require pc self = pc_start
}
end DistErrGenerated

veil module DistErrExpiredLet
type node
network
message ping
var x : Bool := false
/--
error: `y` is not available here: it was bound before a blocking `recv`, `next_round` or loop iteration, and a `let` binding only lives until the node blocks. Store the value in a `var` to keep it across steps.
-/
#guard_msgs in
program (self : node) {
  let y := true
  recv ping
  x := y
}
end DistErrExpiredLet

veil module DistErrRecvInSync
type node
network (synchrony := sync)
message ping
/--
error: `recv` is only available in asynchronous networks; in a synchronous network, end the round with `next_round` and inspect the messages with `received`
-/
#guard_msgs in
program (self : node) {
  recv ping
}
end DistErrRecvInSync

veil module DistErrReceivedInAsync
type node
network
message ping
var x : Bool := false
/--
error: `received` is only available in synchronous networks; in an asynchronous network, use `recv`
-/
#guard_msgs in
program (self : node) {
  x := decide (received ping)
}
end DistErrReceivedInAsync

veil module DistErrMessageArity
type node
network
message vote (b : Bool)
/--
error: message `vote` has 1 field(s), but 0 are given
-/
#guard_msgs in
program (self : node) {
  broadcast vote
}
end DistErrMessageArity

veil module DistErrNested
type node
network
message ping
/--
error: this statement can only appear directly in the program, or inside `if`, `while`, `repeat` and `recv` alternatives
-/
#guard_msgs in
program (self : node) {
  match (1 : Nat) with
  | 0 => broadcast ping
  | _ => pure ()
}
end DistErrNested

veil module DistErrLoopCapture
type node
network
message val (b : Bool)
var x : Bool := false
/--
error: `v` is not available here: it was bound before a blocking `recv`, `next_round` or loop iteration, and a `let` binding only lives until the node blocks. Store the value in a `var` to keep it across steps.
-/
#guard_msgs in
program (self : node) {
  recv (val v)
  while true do
    -- on the next iteration, `v` would be the parameter of the inner `recv`
    x := v
    recv (val v)
}
end DistErrLoopCapture

veil module DistErrFifoSync
type node
/--
error: `order := fifo` only applies to asynchronous networks: a synchronous network delivers the messages of a round together
-/
#guard_msgs in
network (synchrony := sync) (order := fifo)
end DistErrFifoSync

veil module DistErrReadByz
type node
network (faults := byzantine)
var x : Bool := false
/--
error: a node program cannot access `byz`: it tells which nodes are Byzantine, which nodes do not know
-/
#guard_msgs in
program (self : node) {
  x := byz self
}
end DistErrReadByz
