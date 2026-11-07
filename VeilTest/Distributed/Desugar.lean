module

public import Veil

/-! `#desugar_program` prints the plain Veil a `program` compiles to,
preserving choice predicates and optional proof binders. -/

veil module DistDesugar

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
/-- let other :| other ≠ self -/
#guard_msgs(info, substring := true) in
#desugar_program

end DistDesugar

veil module DistDesugarProofPick
type node
network
program (self : node) {
  let other : node :| h : other = self
  have : other = self := h
}
/-- let other : node :| h : other = self -/
#guard_msgs(info, substring := true) in
#desugar_program
end DistDesugarProofPick

veil module DistDesugarNoProgram
type node
network
/-- error: `#desugar_program` must come after a `program` -/
#guard_msgs in
#desugar_program
end DistDesugarNoProgram
