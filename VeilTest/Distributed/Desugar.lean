module

public import Veil

/-! `#desugar_program` prints the plain Veil a `program` compiles to. The
printed code elaborates as plain Veil (checked by hand in
`Examples/Scratch/DesugarRoundTrip.lean`). -/

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
-- TODO: pin the printed code with `#guard_msgs` (needs a rebuild to capture it)
#desugar_program

end DistDesugar

veil module DistDesugarNoProgram
type node
network
/-- error: `#desugar_program` must come after a `program` -/
#guard_msgs in
#desugar_program
end DistDesugarNoProgram
