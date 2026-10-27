module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! A token passes between nodes, and `finish` fires only when no node holds
it. The property holds, but the strengthening it needs, "some node holds the
token", is existential, so the command reports that no universal inductive
invariant exists. -/

veil module TokenPassing

type node
relation tok : node → Bool
individual stopped : Bool

#gen_state

after_init {
  tok N := true
  stopped := false
}

action pass (n m : node) {
  require tok n
  tok n := false
  tok m := true
}

action finish {
  require ∀ N, ¬ tok N
  stopped := true
}

safety [never_stopped] ¬ stopped

#gen_spec

/-- info: No universal inductive invariant over the module's vocabulary proves the safety property -/
#guard_msgs(info, substring := true) in
#synthesize_invariants (expect := no_universal_invariant)

end TokenPassing
