module
public import Veil

veil module DeepBmcTranslation

type node
relation marked : node → Bool
relation edge : node → node → Bool
individual failed : Bool

#gen_state

after_init {
  marked N := false
  edge N M := false
  failed := false
}

action mark (n m : node) {
  marked n := true
  edge n m := true
}

action clear (n m : node) {
  marked n := false
  edge n m := false
}

invariant ¬ failed
#gen_spec

-- This checks that the ordinary BMC pipeline reaches a real UNSAT solver result
-- at a larger depth. Before the early-introduction fix, global normalization
-- under the state binders exhausted simp's default 100,000-step budget here.
-- The two actions change the relations but preserve `failed = false`, keeping
-- solving easy even though preprocessing must traverse every transition.
-- Use the default trusted solver path for this scaling regression; separate
-- semantic tests cover proof reconstruction. No resource limit is raised.
set_option veil.smt.trust true
#guard_msgs(drop info, drop warning) in
unsat trace [failed_unreachable] {
  any 32 actions
  assert failed
}

end DeepBmcTranslation
