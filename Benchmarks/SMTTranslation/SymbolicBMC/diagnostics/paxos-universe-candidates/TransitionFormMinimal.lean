import Veil
set_option Elab.async false
veil module TransitionFormProbe
individual flag : Bool
#gen_state
after_init { flag := false }
transition stay { flag' = flag }
invariant ¬ flag
#gen_spec
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.timeout 10
set_option trace.smt.translate.query true
unsat trace [preserved_flag] {
  any action
  assert flag
} by
  veil_bmc
end TransitionFormProbe
